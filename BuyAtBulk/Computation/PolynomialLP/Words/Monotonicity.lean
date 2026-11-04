import BuyAtBulk.Computation.PolynomialLP.Words.Decision

/-! The closed complexity formulas are fixed semiring-polynomial expressions
and are monotone in dimensions and total stored input length. -/
set_option maxHeartbeats 3000000
namespace BuyAtBulk.PolynomialLP.Trace

@[gcongr] theorem decisionCount_mono {n n' m m' B B' : ℕ}
    (dimension : n ≤ n') (rows : m ≤ m') (bits : B ≤ B') :
    decisionCount n m B ≤ decisionCount n' m' B' := by
  dsimp only [decisionCount, InputTrace.preparationCount, loopBudget, stepBudget,
    roundedStepBudget, stateWidth, matrixProductBudget, workPrecision, feasibilityRounds,
    stoppingRounds, interiorBits, slackBits, phaseGapBits]
  gcongr

@[gcongr] theorem decisionWordBudget_mono {n n' m m' B B' : ℕ}
    (dimension : n ≤ n') (rows : m ≤ m') (bits : B ≤ B') :
    decisionWordBudget n m B ≤ decisionWordBudget n' m' B' := by
  dsimp only [decisionWordBudget, highDecisionWordBudget, InputTrace.preparationWords,
    InputTrace.integerizeWordBudget, InputTrace.boxedWordBudget, InputTrace.scheduleWordBudget,
    InputTrace.scheduleValues, initialWordBudget, highLoopWordBudget, loopWordBudget,
    separationWordBudget, dotWordBudget, matrixProductBudget, stepWordBudget, roundedWordBudget,
    updateWordBudget, matrixWordBudget, quadraticWordBudget, rootWordBudget, rootFuelWordBudget,
    precisionWordBudget, updateQuadraticBudget, rootBudget, updateLeafBudget, centerCellWordBudget,
    shapeCellWordBudget, inflationWordBudget, diagonalWordBudget, roundingCellWordBudget,
    roundingLeafBudget, dyadicWordBudget, executionWidth, stateWidth, unaryWordBudget,
    unaryScanWordBudget, cutWordBudget, zeroWordBudget, workPrecision, feasibilityRounds,
    stoppingRounds, interiorBits, slackBits, phaseGapBits]
  simp only [List.sum_cons, List.sum_nil]
  gcongr

end BuyAtBulk.PolynomialLP.Trace
