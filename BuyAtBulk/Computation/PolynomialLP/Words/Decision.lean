import BuyAtBulk.Computation.PolynomialLP.Words.HighDecision
import BuyAtBulk.Computation.PolynomialLP.Words.LowDimension
import BuyAtBulk.Computation.PolynomialLP.Words.InputSize

/-! Unconditional all-word and count bounds for the complete actual stored
box-feasibility decision, in fixed polynomial formulas of input dimensions
and the binary length computed from its own rational arrays. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP.Trace
open Computation Computation.Runtime Rational
variable {n m : ℕ}

def decisionWordBudget (n m B : ℕ) := highDecisionWordBudget n m B +
  InputTrace.boxedWordBudget n m (2 * B + 2) + unaryWordBudget (m + (n + n)) (2 * B + 6) +
  zeroWordBudget m (2 * B + 2) + n + m + B + 20

theorem decideBoxed_words (input : Stored (n := n) (m := m)) :
    WordsWithin (decisionWordBudget n m (inputBudget input)) (decideBoxed input).events := by
  have cells := input_cellBits input
  cases n with
  | zero =>
    have solve := (zeroSolve_words input _ cells.bounds).mono
      (show _ ≤ decisionWordBudget 0 m (inputBudget input) by dsimp only [decisionWordBudget]; simp only [Nat.add_assoc, Nat.reduceAdd, Nat.zero_add]; omega)
    simp only [decideBoxed, List.append_assoc, wordsWithin_append]
    refine ⟨?_, solve, ?_⟩
    all_goals
      simp only [wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq, and_true]
      dsimp only [decisionWordBudget]
      repeat' apply And.intro
      all_goals omega
  | succ n => cases n with
    | zero =>
      have boxed := (InputTrace.boxedTrace_words input _ cells.coefficients cells.bounds).mono
        (show _ ≤ decisionWordBudget 1 m (inputBudget input) by dsimp only [decisionWordBudget]; simp only [Nat.add_assoc, Nat.reduceAdd, Nat.zero_add]; omega)
      have boxedCells := cells.boxed
      have solve := (unarySolve_words input.boxed _ (fun i => boxedCells.coefficients i 0)
        boxedCells.bounds (boxedCells.objective 0)).mono
        (show _ ≤ decisionWordBudget 1 m (inputBudget input) by dsimp only [decisionWordBudget]; simp only [Nat.add_assoc, Nat.reduceAdd, Nat.zero_add]; omega)
      simp only [decideBoxed, InputTrace.boxedTrace_value, List.append_assoc, wordsWithin_append]
      refine ⟨?_, boxed, solve, ?_⟩
      all_goals
        simp only [wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
          or_false, forall_eq, and_true]
        dsimp only [decisionWordBudget]
        repeat' apply And.intro
        all_goals omega
    | succ n =>
      have high := (highDecision_words input (by omega)).mono
        (show _ ≤ decisionWordBudget (n + 2) m (inputBudget input) by dsimp only [decisionWordBudget]; simp only [Nat.add_assoc, Nat.reduceAdd, Nat.zero_add]; omega)
      simp only [decideBoxed, wordsWithin_append]
      refine ⟨?_, high⟩
      simp only [wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq, and_true]
      dsimp only [decisionWordBudget]
      omega

/-- No solver certificate or runtime field is supplied. Every scalar in the
program's real trace has a source-input-derived polynomial binary width. -/
theorem decideBoxed_runtime (input : Stored (n := n) (m := m)) :
    (decideBoxed input).value = PolynomialLP.decideBoxed input ∧
    (decideBoxed input).events.length ≤ decisionCount n m (inputBudget input) ∧
    WordsWithin (decisionWordBudget n m (inputBudget input)) (decideBoxed input).events :=
  ⟨decideBoxed_value input, decideBoxed_count input, decideBoxed_words input⟩

end BuyAtBulk.PolynomialLP.Trace
