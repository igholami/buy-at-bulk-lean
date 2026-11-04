import BuyAtBulk.Computation.PolynomialLP.OptimizationRuntime

namespace BuyAtBulk.PolynomialLP
open ObjectiveRuntime InputTrace

@[gcongr] theorem optimizerCount_mono {n n' m m' B B' : ℕ}
    (dimension : n≤n') (rows : m≤m') (bits : B≤B') :
    optimizerCount n m B≤optimizerCount n' m' B' := by
  dsimp only [optimizerCount,optimizerRootCount,optimizerRootSize,optimizerK,optimizerL,
    rootCellBits,optimizerFaceL,optimizerRows,coordinateLoopCount,coordinateStepCount,vectorFromListCount]
  gcongr

@[gcongr] theorem optimizerWords_mono {n n' m m' B B' : ℕ}
    (dimension : n≤n') (rows : m≤m') (bits : B≤B') :
    optimizerWords n m B≤optimizerWords n' m' B' := by
  dsimp only [optimizerWords,optimizerRootWords,optimizerRootSize,optimizerK,optimizerL,
    rootCellBits,optimizerFaceL,optimizerRows,coordinateLoopWords,optimizerRootValues,
    integerizeWordBudget,boxedWordBudget]
  simp only [List.sum_cons,List.sum_nil]
  gcongr
end BuyAtBulk.PolynomialLP
