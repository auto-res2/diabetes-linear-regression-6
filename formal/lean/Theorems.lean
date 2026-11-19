import Values
import Claims
open Claims
/-! 各命題の判定。parse_claims.py が生成する。 -/
theorem R01_c1_holds : R01_c1 (observedSha256 := Values.observedSha256) (dataSha256 := Values.dataSha256) (literatureSha256 := Values.literatureSha256) := by decide +kernel
theorem R01_c2_holds : R01_c2 (observedSha256 := Values.observedSha256) (dataSha256 := Values.dataSha256) := by decide +kernel
theorem R01_c3_holds : R01_c3 (dataSha256 := Values.dataSha256) (literatureSha256 := Values.literatureSha256) := by decide +kernel
theorem R02_c1_holds : R02_c1 (nSamples := Values.nSamples) (nFeatures := Values.nFeatures) := by decide +kernel
theorem R02_c2_holds : R02_c2 (featureColumns := Values.featureColumns) := by decide +kernel
theorem R02_c3_holds : R02_c3 (targetColumn := Values.targetColumn) := by decide +kernel
theorem R03_c1_holds : R03_c1 (observedSha256 := Values.observedSha256) (dataSha256 := Values.dataSha256) := by decide +kernel
theorem R03_c2_holds : R03_c2 (dataSha256DeclaredAt := Values.dataSha256DeclaredAt) (firstFullRunAt := Values.firstFullRunAt) := by decide +kernel
theorem R04_c1_holds : R04_c1 (modelInputXSha256 := Values.modelInputXSha256) (loadedXSha256 := Values.loadedXSha256) := by decide +kernel
theorem R05_c1_holds : R05_c1 (targetMean := Values.targetMean) := by decide +kernel
theorem R05_c2_holds : R05_c2 (targetStd := Values.targetStd) := by decide +kernel
theorem R06_c1_holds : R06_c1 (nTrain := Values.nTrain) (nTest := Values.nTest) (nSamples := Values.nSamples) := by decide +kernel
theorem R06_c2_holds : R06_c2 (trainIndex := Values.trainIndex) (testIndex := Values.testIndex) (nSamples := Values.nSamples) := by decide +kernel
theorem R07_c1_holds : R07_c1 (nTest := Values.nTest) (nSamples := Values.nSamples) := by decide +kernel
theorem R07_c2_holds : R07_c2 (splitSeed := Values.splitSeed) := by decide +kernel
theorem R08_c2_holds : R08_c2 := by unfold R08_c2; intros; and_intros <;> rfl
theorem R09_c1_holds : R09_c1 (usedFeatureCount := Values.usedFeatureCount) (nFeatures := Values.nFeatures) := by decide +kernel
theorem R10_c1_holds : R10_c1 (fitFunction := Values.fitFunction) := by decide +kernel
theorem R11_c1_holds : R11_c1 (outputKeys := Values.outputKeys) := by decide +kernel
theorem R12_c1_holds : R12_c1 := by unfold R12_c1; intros; and_intros <;> rfl
theorem R13_c1_holds : R13_c1 := by unfold R13_c1; intros; and_intros <;> rfl
theorem R14_c1_holds : R14_c1 (trainRmse := Values.trainRmse) (trainMse := Values.trainMse) (testRmse := Values.testRmse) (testMse := Values.testMse) (rmseSquaredTolerance := Values.rmseSquaredTolerance) := by decide +kernel
theorem R14_c2_holds : R14_c2 (rmseSquaredToleranceDeclaredAt := Values.rmseSquaredToleranceDeclaredAt) (firstFullRunAt := Values.firstFullRunAt) := by decide +kernel
theorem R14_c3_holds : R14_c3 := by unfold R14_c3; intros; and_intros <;> rfl
theorem R14_c4_holds : R14_c4 := by unfold R14_c4; intros; and_intros <;> rfl
theorem R15_c1_holds : R15_c1 (outputKeys := Values.outputKeys) := by decide +kernel
theorem R17_c1_holds : R17_c1 (envPython := Values.envPython) (envNumpy := Values.envNumpy) (envScikitLearn := Values.envScikitLearn) := by decide +kernel
theorem R18_c1_holds : R18_c1 (repositoryPublic := Values.repositoryPublic) (repositoryFiles := Values.repositoryFiles) := by decide +kernel
theorem R20_c1_holds : R20_c1 (testMse := Values.testMse) := by decide +kernel
theorem R20_c2_holds : R20_c2 (testRmse := Values.testRmse) := by decide +kernel
theorem R20_c3_holds : R20_c3 (testR2 := Values.testR2) := by decide +kernel
theorem R21_c1_holds : R21_c1 (testRmse := Values.testRmse) (targetStd := Values.targetStd) := by decide +kernel
theorem R21_c2_holds : R21_c2 (testRmse := Values.testRmse) (meanPredictorTestRmse := Values.meanPredictorTestRmse) := by decide +kernel
theorem R21_c3_holds : R21_c3 (testRmse := Values.testRmse) (targetStd := Values.targetStd) (meanPredictorTestRmse := Values.meanPredictorTestRmse) := by decide +kernel
theorem R22_c1_holds : R22_c1 (testR2 := Values.testR2) (trainR2 := Values.trainR2) (margin := Values.margin) := by decide +kernel
theorem R22_c2_holds : R22_c2 (trainR2 := Values.trainR2) := by decide +kernel
theorem R22_c3_holds : R22_c3 (marginDeclaredAt := Values.marginDeclaredAt) (firstFullRunAt := Values.firstFullRunAt) := by decide +kernel
theorem R23_c1_holds : R23_c1 (trainMse := Values.trainMse) (testMse := Values.testMse) := by decide +kernel
theorem R24_c1_holds : R24_c1 (trainR2 := Values.trainR2) (trainR2LowerBound := Values.trainR2LowerBound) := by decide +kernel
theorem R24_c2_holds : R24_c2 (testR2 := Values.testR2) (testR2UpperBound := Values.testR2UpperBound) := by decide +kernel
theorem R24_c3_holds : R24_c3 (testR2 := Values.testR2) (trainR2 := Values.trainR2) (margin := Values.margin) (trainMse := Values.trainMse) (testMse := Values.testMse) (trainR2LowerBound := Values.trainR2LowerBound) (testR2UpperBound := Values.testR2UpperBound) := by decide +kernel
theorem R24_c4_holds : R24_c4 (trainR2LowerBoundDeclaredAt := Values.trainR2LowerBoundDeclaredAt) (testR2UpperBoundDeclaredAt := Values.testR2UpperBoundDeclaredAt) (firstFullRunAt := Values.firstFullRunAt) := by decide +kernel
theorem R25_c1_holds : R25_c1 (testR2 := Values.testR2) := by decide +kernel
theorem R26_c1_holds : R26_c1 (trainMse := Values.trainMse) (trainRmse := Values.trainRmse) (trainMae := Values.trainMae) (trainR2 := Values.trainR2) (testMse := Values.testMse) (testRmse := Values.testRmse) (testMae := Values.testMae) (testR2 := Values.testR2) := by decide +kernel
