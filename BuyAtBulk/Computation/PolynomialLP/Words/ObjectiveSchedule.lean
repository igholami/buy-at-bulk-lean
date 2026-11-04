import BuyAtBulk.Computation.PolynomialLP.ObjectiveTrace
import BuyAtBulk.Computation.PolynomialLP.Words.InputSize
import BuyAtBulk.Computation.PolynomialLP.Words.Cells

/-! All metadata, bracket powers and denominator powers of actual exact
objective recovery are computed with polynomial count and word bounds. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace BuyAtBulk.PolynomialLP.ObjectiveRuntime
open Computation Computation.Runtime Rational
variable {n m : ℕ}

theorem objective_cell_bits (input : Stored (n := n) (m := m)) (j : Fin n) :
    (Code.ofRat input.objective[j.val]).bits ≤ objectiveBits input :=
  List.single_le_sum (fun x _ => Nat.zero_le x) _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)

def scheduleValues (n J K : ℕ) : List ℕ :=
  let fourN := 4 * n
  let factor := 2 * (fourN + 1)
  let base := J + K
  let B := factor * (base + 5) + 2
  let E := J + n + 2
  [n, J, K, 1, 2, 3, 4, 5, fourN, fourN + 1, factor, base, base + 5,
    factor * (base + 5), B, J + n, E, B + 1, 2 * (B + 1), E + 2 * (B + 1),
    E + 2 * (B + 1) + 3]

def scheduleWordBudget (n J K : ℕ) :=
  8 * (4 * (n + 1) * (J + 2) + (scheduleValues n J K).sum + 32)

theorem schedule_words (input : Stored (n := n) (m := m)) (K : ℕ) :
    WordsWithin (scheduleWordBudget n (objectiveBits input) K) (schedule input K).events := by
  let J := objectiveBits input
  let B := valueBits input K
  let E := J + n + 2
  let W := scheduleWordBudget n J K
  have vectorWords := (InputTrace.vectorBudget_words input.objective J (objective_cell_bits input)).mono
    (show 4 * (n + 1) * (J + 2) ≤ W by dsimp only [W, scheduleWordBudget]; omega)
  have eBound : E ≤ (scheduleValues n J K).sum := by
    dsimp only [E, scheduleValues]
    simp only [List.sum_cons, List.sum_nil]
    omega
  have depthBound : B + 1 ≤ (scheduleValues n J K).sum := by
    dsimp only [B, valueBits, J, scheduleValues]
    simp only [List.sum_cons, List.sum_nil]
    omega
  have magnitude := (powerTwo_words E).mono
    (show E + 2 ≤ W by dsimp only [W, scheduleWordBudget]; omega)
  have denominator := (powerTwo_words (B + 1)).mono
    (show B + 1 + 2 ≤ W by dsimp only [W, scheduleWordBudget]; omega)
  have upperBits : (Code.ofRat ((2 ^ E : ℕ) : ℚ)).bits = E + 4 := by
    simp [Code.ofRat, Code.bits, Nat.size_pow]
  have lowerBits : (Code.ofRat (-((2 ^ E : ℕ) : ℚ))).bits = E + 4 := by
    rw [Trace.negative_bits, upperBits]
  have oneSize : Nat.size 1 = 1 := rfl
  dsimp only [E, B, J] at magnitude denominator upperBits lowerBits
  have budgetValue : (InputTrace.vectorBudget input.objective).value = J := by
    simp only [InputTrace.vectorBudget_value, J, objectiveBits]
  simp only [schedule, Traced.bind_events, Traced.bind_value, budgetValue,
    natMul, addNat, emit_value, powerTwo_value, ratCast, List.append_assoc, wordsWithin_append]
  simp only [E, B, J, objectiveBits, valueBits, InputTrace.vectorBudget_value] at *
  simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, and_true]
  repeat' apply And.intro
  all_goals first
    | exact vectorWords
    | exact magnitude
    | exact denominator
    | (try simp only [upperBits, lowerBits, Nat.size_pow, Trace.negative_bits]
       first
       | (apply (Nat.size_le.mpr Nat.lt_two_pow_self).trans
          dsimp only [W, scheduleWordBudget, scheduleValues, J, B, E]
          simp only [List.sum_cons, List.sum_nil, objectiveBits]
          omega)
       | (dsimp only [W, scheduleWordBudget, scheduleValues, J, B, E]
          simp only [List.sum_cons, List.sum_nil, objectiveBits]
          omega))

@[gcongr] theorem scheduleWordBudget_mono {n n' J J' K K' : ℕ}
    (dimension : n ≤ n') (objective : J ≤ J') (coordinate : K ≤ K') :
    scheduleWordBudget n J K ≤ scheduleWordBudget n' J' K' := by
  dsimp only [scheduleWordBudget, scheduleValues]
  simp only [List.sum_cons, List.sum_nil]
  gcongr

end BuyAtBulk.PolynomialLP.ObjectiveRuntime
