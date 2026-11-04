import BuyAtBulk.Computation.PolynomialLP.RecoveryRuntime

namespace BuyAtBulk.PolynomialLP.ObjectiveRuntime
@[gcongr] theorem recoverCount_mono {n n' m m' L L' K K' : ℕ}
    (dimension : n≤n') (rows : m≤m') (cells : L≤L') (vertices : K≤K') :
    recoverCount n m L K ≤ recoverCount n' m' L' K' := by
  dsimp only [recoverCount,scheduleCount,reconstructionCount,reconstructionSize,
    queryCount,querySize,queryWidth,gridHeight,searchDepth,searchRounds,valueBudget]
  gcongr

@[gcongr] theorem recoverWordBudget_mono {n n' m m' L L' K K' : ℕ}
    (dimension : n≤n') (rows : m≤m') (cells : L≤L') (vertices : K≤K') :
    recoverWordBudget n m L K ≤ recoverWordBudget n' m' L' K' := by
  dsimp only [recoverWordBudget,reconstructionWordBudget,reconstructionSize,
    ReconstructionRuntime.wordBudget,queryWordBudget,querySize,queryWidth,gridHeight,
    searchDepth,searchRounds,valueBudget]
  gcongr
end BuyAtBulk.PolynomialLP.ObjectiveRuntime
