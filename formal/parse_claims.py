"""パーサー。claims.json を読み、検証器を呼び、Lean の値と定理のファイルを書き、Lean の出力から判定を読む。"""
import json
import re
from fractions import Fraction
from pathlib import Path

from verifiers import QUERIES

FORMAL = Path(__file__).parent
# 型ごとの、Lean での書き方
LITERAL = {
    "String": json.dumps,
    "Bool": lambda value: str(bool(value)).lower(),
    "ℕ": lambda value: str(int(value)),
    "ℚ": lambda value: f"(({Fraction(value).numerator} : ℚ) / {Fraction(value).denominator})",
}
HEADER = ["import Values", "import Claims", "open Claims"]


def lean_literal(lean_type: str, value) -> str:
    if lean_type.startswith("List "):
        return "[" + ", ".join(lean_literal(lean_type.removeprefix("List "), item) for item in value) + "]"
    return LITERAL[lean_type](value)


def read_claims() -> dict:
    record = json.loads((FORMAL / "claims.json").read_text(encoding="utf-8"))
    unknown = [claim["id"] for claim in record["claims"] if claim["sentence"] not in record["sentences"]]
    if unknown:
        raise ValueError(f"存在しない文を指している: {unknown}")
    # 分解器が付けた印と、形式化の形を突き合わせる。定義は値を受けず、それ以外は値を受けるか、検証器が無い
    mismatched = [claim["id"] for claim in record["claims"]
                  if claim.get("definition", False) == bool(claim["formalization"]["arguments"]) and "unverifiable" not in claim]
    if mismatched:
        raise ValueError(f"定義の印と、値の引数が食い違っている: {mismatched}")
    return record


def query_values(record: dict, repository: str, mode: str) -> tuple[dict, dict[str, str]]:
    """宣言していない変数を、検証器に問い合わせる。(JSON の値, 取れなかった理由) を返す。"""
    values, errors = {}, {}
    for name, variable in record["variables"].items():
        if "declared" in variable:
            continue
        try:
            values[name] = QUERIES[variable["verifier"]][variable["query"]](repository, mode, name, **variable.get("args", {}))
        except Exception as error:  # 取れなかった値を使う claim だけを、未検証にする
            errors[name] = str(error)
    return values, errors


def write_values(record: dict) -> None:
    """スキーマの宣言した値（declared）と検証済みの値（verified）から、Values.lean を書く。"""
    lines = ["import Mathlib", "/-! スキーマ（claims.json）の宣言した値と検証済みの値。parse_claims.py が生成する。手で編集しない。 -/", "namespace Values"]
    for name, variable in record["variables"].items():
        value = variable["declared"] if "declared" in variable else variable.get("verified", {}).get("value")
        if value is not None:
            lines.append(f"def {name} : {variable['type']} := {lean_literal(variable['type'], value)}")
    (FORMAL / "lean" / "Values.lean").write_text("\n".join(lines + ["end Values", ""]), encoding="utf-8")


def proposition(claim: dict) -> str:
    """命題名に、値を名前付きの引数として付ける。"""
    formalization = claim["formalization"]
    return " ".join([formalization["proposition_name"]] + [f"({name} := Values.{name})" for name in formalization["arguments"]])


def candidates(claim: dict) -> list[str]:
    """命題が真である定理と、偽である（否定の）定理。通ったほうが判定になる。有理数の比較は decide では簡約が止まるので、kernel に評価させる。"""
    name, statement = claim["id"], proposition(claim)
    # 検証器が無い claims は、公理が宣言されていることだけを見る
    if "unverifiable" in claim:
        return [f"#print axioms {name}_axiom"]
    # 定義は、定義を展開すれば両辺が一致する等式（とその連言）だけを通す
    if claim.get("definition"):
        return [f"theorem {name}_holds : {statement} := by unfold {statement}; intros; and_intros <;> rfl",
                f"#print axioms {name}_holds"]
    return [f"theorem {name}_holds : {statement} := by decide +kernel",
            f"theorem {name}_fails : ¬ ({statement}) := by decide +kernel",
            f"#print axioms {name}_holds", f"#print axioms {name}_fails"]


def write_candidates(claims: list[dict]) -> Path:
    """claims の定理の候補と公理の確認を、1 つのファイルに書く。Lean の起動を 1 回で済ませる。"""
    lines = HEADER + [line for claim in claims for line in candidates(claim)]
    path = FORMAL / "lean" / "Candidates.lean"
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return path


def read_axioms(lean_output: str) -> dict[str, list[str] | None]:
    """定理ごとの、依存する公理。証明が通らなかった定理は sorryAx に依存する。出力に無い定理は None。名前の Claims. は外す。"""
    flat = re.sub(r"\s+", " ", lean_output)
    short = lambda name: name.removeprefix("Claims.")
    axioms = {short(name): [] for name in re.findall(r"'([\w.]+)' does not depend on any axioms", flat)}
    axioms |= {short(name): [short(axiom) for axiom in listed.split(", ")]
               for name, listed in re.findall(r"'([\w.]+)' depends on axioms: \[([^\]]*)\]", flat)}
    return axioms


def judge(claim: dict, allowed_axioms: set[str], axioms: dict) -> dict:
    """真か偽か判定できずか。通った定理が、宣言した公理の外に依存していたら、判定できずにする。"""
    for verdict, suffix in (("真", "holds"), ("偽", "fails")):
        used = axioms.get(f"{claim['id']}_{suffix}")
        if used is not None and "sorryAx" not in used:
            if set(used) <= allowed_axioms:
                return {"verdict": verdict, "axioms": sorted(used)}
            return {"verdict": "判定できず", "reason": f"宣言した公理の外に依存している: {sorted(set(used) - allowed_axioms)}"}
    return {"verdict": "判定できず", "reason": "真の定理も偽の定理も通らなかった"}


def write_theorems(claims: list[dict], results: dict) -> None:
    """判定が付いた命題を、真なら定理、偽なら否定の定理として Theorems.lean に書く。"""
    lines = HEADER + ["/-! 各命題の判定。parse_claims.py が生成する。 -/"]
    lines += [candidates(claim)[results[claim["id"]]["verdict"] == "偽"] for claim in claims
              if results[claim["id"]].get("verdict") in ("真", "偽")]
    (FORMAL / "lean" / "Theorems.lean").write_text("\n".join(lines) + "\n", encoding="utf-8")
