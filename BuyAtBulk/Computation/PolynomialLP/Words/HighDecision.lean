import BuyAtBulk.Computation.PolynomialLP.Trace.Decision
import BuyAtBulk.Computation.PolynomialLP.Words.Loop
import BuyAtBulk.Computation.PolynomialLP.Words.Initial

/-! Source-input-derived uniform word widths for the complete rational
ellipsoid decision, including relaxed bounds and every possibly infeasible run. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP.Trace
open Computation Computation.Runtime Rational
variable {n m : ℕ}

def executionWidth (n L : ℕ) := stateWidth n L + 2 * (L + slackBits n L + 8) + 40

def highLoopWordBudget (n m B : ℕ) :=
  let L := (n + 2) * B
  loopWordBudget n (m + (n + n)) (feasibilityRounds n L) (executionWidth n L)

theorem highLoop_words (input : Stored (n := n) (m := m)) (dimension : 2 ≤ n) :
    WordsWithin (highLoopWordBudget n m (inputBudget input))
      (loop ((integerize input).boxed.slack (feasibilitySlack n (integerL input)))
        (workPrecision n (feasibilityRounds n (integerL input)))
        (feasibilityRounds n (integerL input)) (Ellipsoid.initial n)).events := by
  change WordsWithin (loopWordBudget n (m + (n + n)) (feasibilityRounds n (integerL input))
    (executionWidth n (integerL input))) _
  apply loop_words _ _ _ 0 (executionWidth n (integerL input))
  · dsimp only [executionWidth]; omega
  · intro i j
    have bound := (InputTrace.integerized_boxed_bits input).1 i j
    simp only [Stored.slack]
    dsimp only [executionWidth]
    omega
  · intro i
    have bound := (InputTrace.integerized_boxed_bits input).2 i
    have epsilon := InputTrace.dyadicReciprocal_bits (slackBits n (integerL input))
    have sum := ratAdd_result_bits (integerize input).boxed.bounds[i.val]
      (feasibilitySlack n (integerL input))
    simp only [Stored.slack, Vector.getElem_map]
    change (Code.ofRat (feasibilitySlack n (integerL input))).bits ≤ _ at epsilon
    dsimp only [executionWidth]
    omega
  · dsimp only [executionWidth, stateWidth]; omega
  · omega
  · exact initial_invariant n dimension
  · intro i
    have halfBits : (Code.ofRat ((1 : ℚ) / 2)).bits = 5 := by
      norm_num [Code.ofRat, Code.bits, show Nat.size 2 = 2 by decide]
    simp only [Ellipsoid.initial, Vector.getElem_replicate, halfBits]
    dsimp only [executionWidth]
    omega
  · intro i j
    have dim := natural_rational_bits n
    have zero : (Code.ofRat 0).bits = 3 := by decide
    simp only [Ellipsoid.initial, Vector.getElem_ofFn]
    dsimp only [executionWidth, stateWidth]
    split_ifs <;> omega

def highDecisionWordBudget (n m B : ℕ) := InputTrace.preparationWords n m B + initialWordBudget n +
  highLoopWordBudget n m B + n + m + 10

theorem highDecision_words (input : Stored (n := n) (m := m)) (dimension : 2 ≤ n) :
    WordsWithin (highDecisionWordBudget n m (inputBudget input)) (highDecision input).events := by
  have preparation := (InputTrace.prepareTrace_words input).mono
    (show _ ≤ highDecisionWordBudget n m (inputBudget input) by dsimp only [highDecisionWordBudget]; omega)
  have start := (initial_words n).mono
    (show _ ≤ highDecisionWordBudget n m (inputBudget input) by dsimp only [highDecisionWordBudget]; omega)
  have iterations := (highLoop_words input dimension).mono
    (show _ ≤ highDecisionWordBudget n m (inputBudget input) by dsimp only [highDecisionWordBudget]; omega)
  simp only [highDecision, InputTrace.prepareTrace_value, initial_value,
    List.append_assoc, wordsWithin_append]
  refine ⟨preparation, start, iterations, ?_⟩
  simp only [wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq, and_true]
  dsimp only [highDecisionWordBudget]
  constructor <;> omega

end BuyAtBulk.PolynomialLP.Trace
