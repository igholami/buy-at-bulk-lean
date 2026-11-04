import BuyAtBulk.Computation.PolynomialLP.Trace.Separation
import BuyAtBulk.Computation.PolynomialLP.Words.Matrix

/-! Complete operand-width bounds for actual rational row separation scans. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP.Trace
open Computation Computation.Runtime Rational
variable {n m : ℕ}

def separationWordBudget (n m L : ℕ) := m + n + dotWordBudget n n L + matrixProductBudget n L + L + 10

theorem violated_words (input : Stored (n := n) (m := m)) (x : Vector ℚ n) (i : Fin m)
    (L : ℕ) (constant : 5 ≤ L)
    (coefficients : ∀ j : Fin n, (Code.ofRat input.coefficients[i.val][j.val]).bits + 1 ≤ L)
    (bounds : (Code.ofRat input.bounds[i.val]).bits + 1 ≤ L)
    (coordinates : ∀ j : Fin n, (Code.ofRat x[j.val]).bits + 1 ≤ L) :
    WordsWithin (separationWordBudget n m L) (violated input x i).events := by
  let K := separationWordBudget n m L
  have index : i.val.size ≤ m := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt i.isLt)
  have arithmetic := (dotScan_words input.coefficients[i.val] x (List.finRange n) L constant coefficients coordinates).mono
    (show _ ≤ K by simp only [List.length_finRange]; dsimp only [K, separationWordBudget]; omega)
  have result := dotScan_bits input.coefficients[i.val] x (List.finRange n) L constant coefficients coordinates
  simp only [List.length_finRange] at result
  simp only [violated, Traced.bind_events, Traced.bind_value, emit_value, indexList_value,
    wordsWithin_append]
  refine ⟨?_, indexList_words n _ (by dsimp only [K, separationWordBudget]; omega), arithmetic, ?_, ?_⟩
  all_goals
    simp only [readRat, ratLess, emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true, dotScan_value]
    dsimp only [K, separationWordBudget, matrixProductBudget]
    simp only [dotScan_value] at result
    repeat' apply And.intro
    all_goals omega

theorem separationScan_words (input : Stored (n := n) (m := m)) (x : Vector ℚ n)
    (rows : List (Fin m)) (L : ℕ) (constant : 5 ≤ L)
    (coefficients : ∀ i : Fin m, ∀ j : Fin n, (Code.ofRat input.coefficients[i.val][j.val]).bits + 1 ≤ L)
    (bounds : ∀ i : Fin m, (Code.ofRat input.bounds[i.val]).bits + 1 ≤ L)
    (coordinates : ∀ j : Fin n, (Code.ofRat x[j.val]).bits + 1 ≤ L) :
    WordsWithin (separationWordBudget n m L) (separationScan input x rows).events := by
  induction rows with
  | nil => exact wordsWithin_nil _
  | cons i rest ih =>
    have index : i.val.size ≤ m := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt i.isLt)
    have row := violated_words input x i L constant (coefficients i) (bounds i) coordinates
    simp only [separationScan, Traced.bind_events, Traced.bind_value, emit_value,
      branch, wordsWithin_append]
    refine ⟨?_, row, ?_, ?_⟩
    · simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq, and_true]
      dsimp only [separationWordBudget]
      omega
    · simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq, and_true]
      dsimp only [separationWordBudget]
      omega
    · change WordsWithin _ (if (violated input x i).value then Traced.pure (some i) else separationScan input x rest).events
      split_ifs
      · exact wordsWithin_nil _
      · exact ih

theorem separate_words (input : Stored (n := n) (m := m)) (x : Vector ℚ n)
    (L : ℕ) (constant : 5 ≤ L)
    (coefficients : ∀ i : Fin m, ∀ j : Fin n, (Code.ofRat input.coefficients[i.val][j.val]).bits + 1 ≤ L)
    (bounds : ∀ i : Fin m, (Code.ofRat input.bounds[i.val]).bits + 1 ≤ L)
    (coordinates : ∀ j : Fin n, (Code.ofRat x[j.val]).bits + 1 ≤ L) :
    WordsWithin (separationWordBudget n m L) (separate input x).events := by
  simp only [separate, Traced.bind_events, Traced.bind_value, indexList_value, wordsWithin_append]
  exact ⟨indexList_words m _ (by dsimp only [separationWordBudget]; omega),
    separationScan_words input x _ L constant coefficients bounds coordinates⟩

end BuyAtBulk.PolynomialLP.Trace
