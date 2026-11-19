import Mathlib
/-!
レポートの各文の claims を、命題として書いたもの。
値はすべて引数で受ける。値を入れるのは parse_claims.py が生成する Theorems.lean。
検証器が無い claims は、対象を opaque な定数として置き、公理として宣言する（末尾）。
-/
namespace Claims


/-! ## R01 -/
abbrev R01_c2 (observedSha256 dataSha256 : String) : Prop := observedSha256 = dataSha256
abbrev R01_c3 (dataSha256 literatureSha256 : String) : Prop := dataSha256 = literatureSha256
abbrev R01_c1 (observedSha256 dataSha256 literatureSha256 : String) : Prop :=
  R01_c2 observedSha256 dataSha256 ∧ R01_c3 dataSha256 literatureSha256
/-- 検証器なし。文献 [1] が示すファイルは、配布元の URL のファイルである。 -/
abbrev R01_c4 (literatureFileSha256 distributedFileSha256 : String) : Prop :=
  literatureFileSha256 = distributedFileSha256

/-! ## R02 -/
abbrev R02_c1 (nSamples nFeatures : ℕ) : Prop := nSamples = 442 ∧ nFeatures = 10
abbrev R02_c2 (featureColumns : List String) : Prop :=
  featureColumns = ["AGE", "SEX", "BMI", "BP", "S1", "S2", "S3", "S4", "S5", "S6"]
abbrev R02_c3 (targetColumn : String) : Prop := targetColumn = "Y"

/-! ## R03 -/
abbrev R03_c1 (observedSha256 dataSha256 : String) : Prop := observedSha256 = dataSha256
abbrev R03_c2 (dataSha256DeclaredAt firstFullRunAt : ℕ) : Prop := dataSha256DeclaredAt ≤ firstFullRunAt
/-- 検証器なし。一致しないファイルでは実行されない。 -/
abbrev R03_c3 (sha256Of : String → String) (runs : String → Prop) (dataSha256 : String) : Prop :=
  ∀ file, sha256Of file ≠ dataSha256 → ¬ runs file

/-! ## R04 -/
abbrev R04_c1 (modelInputXSha256 loadedXSha256 : String) : Prop := modelInputXSha256 = loadedXSha256

/-! ## R05 -/
abbrev R05_c1 (targetMean : ℚ) : Prop := (round (targetMean / 0.1) : ℚ) * 0.1 = 152.1
abbrev R05_c2 (targetStd : ℚ) : Prop := (round (targetStd / 0.1) : ℚ) * 0.1 = 77.0
/-- 検証器なし。出力の平均と標準偏差は、全件に対して定義どおりに計算した値をそのまま書き出したものである。 -/
abbrev R05_c3 (targetStatsComputedAsSpecified : Bool) : Prop := targetStatsComputedAsSpecified = true

/-! ## R06 -/
abbrev R06_c1 (nTrain nTest nSamples : ℕ) : Prop := nTrain = 353 ∧ nTest = 89 ∧ nTrain + nTest = nSamples
abbrev R06_c2 (trainIndex testIndex : List ℕ) (nSamples : ℕ) : Prop :=
  Disjoint trainIndex.toFinset testIndex.toFinset ∧
  trainIndex.toFinset ∪ testIndex.toFinset = Finset.range nSamples
/-- 検証器なし。分割は、シードを入れた並べ替えの手続きで決まる。 -/
abbrev R06_c3 (shuffleSplit : ℕ → List ℕ × List ℕ) (trainIndex testIndex : List ℕ) (splitSeed : ℕ) : Prop :=
  (trainIndex, testIndex) = shuffleSplit splitSeed

/-! ## R07 -/
abbrev R07_c1 (nTest nSamples : ℕ) : Prop := (nTest : ℤ) = ⌈(0.2 : ℚ) * nSamples⌉
abbrev R07_c2 (splitSeed : ℕ) : Prop := splitSeed = 0

/-! ## R08 -/
/-- 線形回帰モデル（式 (3)）。 -/
def linearModel {p : ℕ} (β₀ : ℝ) (β : Fin p → ℝ) (x : Fin p → ℝ) : ℝ := β₀ + ∑ j, β j * x j
/-- 検証器なし。係数は、訓練データ上の残差の二乗和を最小にする。 -/
abbrev R08_c1 {n p : ℕ} (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (β₀ : ℝ) (β : Fin p → ℝ) : Prop :=
  ∀ b₀ b, ∑ i, (y i - linearModel β₀ β (X i)) ^ 2 ≤ ∑ i, (y i - linearModel b₀ b (X i)) ^ 2
/-- 定義。線形回帰モデルは式 (3) である。 -/
abbrev R08_c2 : Prop := ∀ (p : ℕ) (β₀ : ℝ) (β x : Fin p → ℝ), linearModel β₀ β x = β₀ + ∑ j, β j * x j

/-! ## R09 -/
abbrev R09_c1 (usedFeatureCount nFeatures : ℕ) : Prop := usedFeatureCount = nFeatures
/-- 検証器なし。正則化の係数は 0 である。 -/
abbrev R09_c2 (penaltyWeight : ℚ) : Prop := penaltyWeight = 0

/-! ## R10 -/
abbrev R10_c1 (fitFunction : String) : Prop := fitFunction = "sklearn.linear_model.LinearRegression"

/-! ## R11、R15 -/
abbrev R11_c1 (outputKeys : List String) : Prop :=
  ["trainMse", "trainRmse", "trainMae", "trainR2", "testMse", "testRmse", "testMae", "testR2"] ⊆ outputKeys
abbrev R15_c1 (outputKeys : List String) : Prop := R11_c1 outputKeys

/-! ## R12、R13 -/
/-- 目的変数の平均 ȳ。 -/
noncomputable def mean {n : ℕ} (y : Fin n → ℝ) : ℝ := (1 / (n : ℝ)) * ∑ i, y i
noncomputable def mse {n : ℕ} (y ŷ : Fin n → ℝ) : ℝ := (1 / (n : ℝ)) * ∑ i, (y i - ŷ i) ^ 2
noncomputable def r2 {n : ℕ} (y ŷ : Fin n → ℝ) : ℝ :=
  1 - (∑ i, (y i - ŷ i) ^ 2) / ∑ i, (y i - mean y) ^ 2
/-- 定義。MSE と R² は式 (4)、(5) である。 -/
abbrev R12_c1 : Prop := ∀ (n : ℕ) (y ŷ : Fin n → ℝ),
  mse y ŷ = (1 / (n : ℝ)) * ∑ i, (y i - ŷ i) ^ 2 ∧
  r2 y ŷ = 1 - (∑ i, (y i - ŷ i) ^ 2) / ∑ i, (y i - mean y) ^ 2
/-- 定義。ȳ は当該データにおける目的変数の平均である。 -/
abbrev R13_c1 : Prop := ∀ (n : ℕ) (y : Fin n → ℝ), mean y = (1 / (n : ℝ)) * ∑ i, y i

/-! ## R14 -/
abbrev R14_c1 (trainRmse trainMse testRmse testMse rmseSquaredTolerance : ℚ) : Prop :=
  |trainRmse ^ 2 - trainMse| ≤ rmseSquaredTolerance ∧ |testRmse ^ 2 - testMse| ≤ rmseSquaredTolerance
abbrev R14_c2 (rmseSquaredToleranceDeclaredAt firstFullRunAt : ℕ) : Prop :=
  rmseSquaredToleranceDeclaredAt ≤ firstFullRunAt
noncomputable def mae {n : ℕ} (y ŷ : Fin n → ℝ) : ℝ := (1 / (n : ℝ)) * ∑ i, |y i - ŷ i|
noncomputable def rmse {n : ℕ} (y ŷ : Fin n → ℝ) : ℝ := Real.sqrt (mse y ŷ)
/-- 定義。RMSE は MSE の平方根である。 -/
abbrev R14_c4 : Prop := ∀ (n : ℕ) (y ŷ : Fin n → ℝ), rmse y ŷ = Real.sqrt (mse y ŷ)
/-- 定義。MAE は |y_i − ŷ_i| の平均である。 -/
abbrev R14_c3 : Prop := ∀ (n : ℕ) (y ŷ : Fin n → ℝ), mae y ŷ = (1 / (n : ℝ)) * ∑ i, |y i - ŷ i|

/-! ## R16、R17 -/
/-- 検証器なし。元の実験の計算機。 -/
abbrev R16_c1 (envCpuModel : String) (envCpuLogicalCores : ℕ) (envMemoryGib : ℚ) : Prop :=
  envCpuModel = "Intel(R) Core(TM) i5-10400 CPU @ 2.90GHz" ∧ envCpuLogicalCores = 12 ∧ envMemoryGib = 7.7
/-- 検証器なし。使った GPU の数は 0 である。 -/
abbrev R16_c2 (gpuCount : ℕ) : Prop := gpuCount = 0
abbrev R17_c1 (envPython envNumpy envScikitLearn : String) : Prop :=
  envPython = "3.13.3" ∧ envNumpy = "2.3.4" ∧ envScikitLearn = "1.7.2"

/-! ## R18 -/
abbrev R18_c1 (repositoryPublic : Bool) (repositoryFiles : List String) : Prop :=
  repositoryPublic = true ∧ ["src/run_experiment.py", "results/metrics.json"] ⊆ repositoryFiles

/-! ## R19 -/
/-- 検証器なし。表 2 に、訓練とテストのそれぞれについて、4 つの指標の欄がある。 -/
abbrev R19_c1 (tableKeys : ℕ → String → List String) : Prop :=
  ∀ split ∈ ["train", "test"], ["mse", "rmse", "mae", "r2"] ⊆ tableKeys 2 split

/-! ## R20 -/
abbrev R20_c1 (testMse : ℚ) : Prop := (round (testMse / 0.1) : ℚ) * 0.1 = 3424.3
abbrev R20_c2 (testRmse : ℚ) : Prop := (round (testRmse / 0.1) : ℚ) * 0.1 = 58.5
abbrev R20_c3 (testR2 : ℚ) : Prop := (round (testR2 / 0.001) : ℚ) * 0.001 = 0.332

/-! ## R21 -/
abbrev R21_c1 (testRmse targetStd : ℚ) : Prop := testRmse < targetStd
abbrev R21_c2 (testRmse meanPredictorTestRmse : ℚ) : Prop := testRmse < meanPredictorTestRmse
abbrev R21_c3 (testRmse targetStd meanPredictorTestRmse : ℚ) : Prop :=
  R21_c1 testRmse targetStd → R21_c2 testRmse meanPredictorTestRmse

/-! ## R22 -/
abbrev R22_c1 (testR2 trainR2 margin : ℚ) : Prop := testR2 + margin ≤ trainR2
abbrev R22_c2 (trainR2 : ℚ) : Prop := (round (trainR2 / 0.001) : ℚ) * 0.001 = 0.554
abbrev R22_c3 (marginDeclaredAt firstFullRunAt : ℕ) : Prop := marginDeclaredAt ≤ firstFullRunAt
/-- 検証器なし。出力の R² は、各データに対して式 (5) のとおりに計算され、そのまま書き出されている。 -/
abbrev R22_c4 (r2ComputedAsSpecified : Bool) : Prop := r2ComputedAsSpecified = true

/-! ## R23 -/
abbrev R23_c1 (trainMse testMse : ℚ) : Prop := trainMse < testMse

/-! ## R24 -/
abbrev R24_c1 (trainR2 trainR2LowerBound : ℚ) : Prop := trainR2LowerBound ≤ trainR2
abbrev R24_c2 (testR2 testR2UpperBound : ℚ) : Prop := testR2 ≤ testR2UpperBound
abbrev R24_c3 (testR2 trainR2 margin trainMse testMse trainR2LowerBound testR2UpperBound : ℚ) : Prop :=
  R22_c1 testR2 trainR2 margin ∧ R23_c1 trainMse testMse →
    R24_c1 trainR2 trainR2LowerBound ∧ R24_c2 testR2 testR2UpperBound
abbrev R24_c4 (trainR2LowerBoundDeclaredAt testR2UpperBoundDeclaredAt firstFullRunAt : ℕ) : Prop :=
  trainR2LowerBoundDeclaredAt ≤ firstFullRunAt ∧ testR2UpperBoundDeclaredAt ≤ firstFullRunAt

/-! ## R25 -/
abbrev R25_c1 (testR2 : ℚ) : Prop := 0 < testR2 ∧ testR2 < 1

/-! ## R26 -/
abbrev R26_c1 (trainMse trainRmse trainMae trainR2 testMse testRmse testMae testR2 : ℚ) : Prop :=
  (round (trainMse / 0.1) : ℚ) * 0.1 = 2734.8 ∧ (round (trainRmse / 0.1) : ℚ) * 0.1 = 52.3 ∧
  (round (trainMae / 0.1) : ℚ) * 0.1 = 42.6 ∧ (round (trainR2 / 0.001) : ℚ) * 0.001 = 0.554 ∧
  (round (testMse / 0.1) : ℚ) * 0.1 = 3424.3 ∧ (round (testRmse / 0.1) : ℚ) * 0.1 = 58.5 ∧
  (round (testMae / 0.1) : ℚ) * 0.1 = 46.2 ∧ (round (testR2 / 0.001) : ℚ) * 0.001 = 0.332

/-! ## 検証器が無い claims の公理
対象は検証器で観測しないので、opaque な定数として置く。 -/
namespace Unobserved
opaque literatureFileSha256 : String
opaque distributedFileSha256 : String
opaque sha256Of : String → String
opaque runs : String → Prop
opaque dataSha256 : String
opaque targetStatsComputedAsSpecified : Bool
opaque shuffleSplit : ℕ → List ℕ × List ℕ
opaque trainIndex : List ℕ
opaque testIndex : List ℕ
opaque splitSeed : ℕ
noncomputable opaque trainX : Fin 353 → Fin 10 → ℝ
noncomputable opaque trainY : Fin 353 → ℝ
noncomputable opaque β₀ : ℝ
noncomputable opaque β : Fin 10 → ℝ
opaque penaltyWeight : ℚ
opaque envCpuModel : String
opaque envCpuLogicalCores : ℕ
opaque envMemoryGib : ℚ
opaque gpuCount : ℕ
opaque tableKeys : ℕ → String → List String
opaque r2ComputedAsSpecified : Bool
end Unobserved

open Unobserved in
axiom R01_c4_axiom : R01_c4 literatureFileSha256 distributedFileSha256
open Unobserved in
axiom R03_c3_axiom : R03_c3 sha256Of runs dataSha256
open Unobserved in
axiom R05_c3_axiom : R05_c3 targetStatsComputedAsSpecified
open Unobserved in
axiom R06_c3_axiom : R06_c3 shuffleSplit trainIndex testIndex splitSeed
open Unobserved in
axiom R08_c1_axiom : R08_c1 trainX trainY β₀ β
open Unobserved in
axiom R09_c2_axiom : R09_c2 penaltyWeight
open Unobserved in
axiom R16_c1_axiom : R16_c1 envCpuModel envCpuLogicalCores envMemoryGib
open Unobserved in
axiom R16_c2_axiom : R16_c2 gpuCount
open Unobserved in
axiom R19_c1_axiom : R19_c1 tableKeys
open Unobserved in
axiom R22_c4_axiom : R22_c4 r2ComputedAsSpecified

end Claims
