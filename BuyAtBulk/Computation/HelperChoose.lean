import BuyAtBulk.Computation.HelperExpressions
import BuyAtBulk.Computation.Rational.Compare

/-! Deterministic helper selection via explicit unreduced integer arithmetic.
The expression evaluation schedule is polynomial in rows and vertices. -/
namespace BuyAtBulk.Computation.HelperExpressions
open Rational
variable {V R : Type}

theorem potential_eq_mathematical [Fintype R] [DecidableEq R]
    (buying probability : V → ℚ) (factor : R → V → ℚ)
    (amplitude : R → ℚ) (fixedCost normalization : ℚ) (rows : List R)
    (nodup : rows.Nodup) (complete : rows.toFinset = Finset.univ) (selected remaining : List V) :
    (potential buying probability factor amplitude fixedCost normalization rows selected remaining).value =
      ConditionalExpectation.potential buying probability factor amplitude fixedCost normalization selected remaining := by
  rw [potential_value]
  unfold ConditionalExpectation.potential
  congr 1
  have sum := List.sum_toFinset
    (fun r => amplitude r * (selected.map (factor r)).prod *
      (remaining.map fun v => 1 - probability v + probability v * factor r v).prod) nodup
  rw [complete] at sum
  exact sum.symm

/-- Returned selection and counted expression-node visits plus branch tests.
Integer comparison uses cross-products, with no normalization oracle. -/
def chooseScheduled (buying probability : V → ℚ) (factor : R → V → ℚ)
    (amplitude : R → ℚ) (fixedCost normalization : ℚ) (rows : List R) :
    List V → List V → List V × ℕ
  | selected, [] => (selected, 0)
  | selected, v :: remaining =>
      if probability v = 0 then
        let recursive := chooseScheduled buying probability factor amplitude fixedCost normalization rows selected remaining
        (recursive.1, recursive.2 + 1)
      else
        let left := (potential buying probability factor amplitude fixedCost normalization rows selected remaining).evaluate
        let right := (potential buying probability factor amplitude fixedCost normalization rows (v :: selected) remaining).evaluate
        let recursive := if left.1.lessEqual right.1 then
            chooseScheduled buying probability factor amplitude fixedCost normalization rows selected remaining
          else chooseScheduled buying probability factor amplitude fixedCost normalization rows (v :: selected) remaining
        (recursive.1, recursive.2 + left.2 + right.2 + 2)
termination_by _ remaining => remaining.length

theorem chooseScheduled_refines [Fintype R] [DecidableEq R]
    (buying probability : V → ℚ) (factor : R → V → ℚ)
    (amplitude : R → ℚ) (fixedCost normalization : ℚ) (rows : List R)
    (nodup : rows.Nodup) (complete : rows.toFinset = Finset.univ) (selected remaining : List V) :
    (chooseScheduled buying probability factor amplitude fixedCost normalization rows selected remaining).1 =
      ConditionalExpectation.choose buying probability factor amplitude fixedCost normalization selected remaining := by
  induction remaining generalizing selected with
  | nil => simp [chooseScheduled, ConditionalExpectation.choose]
  | cons v remaining ih =>
    simp only [chooseScheduled, ConditionalExpectation.choose]
    by_cases zero : probability v = 0
    · simp only [zero, if_pos, true_or]
      exact ih selected
    · simp only [zero, if_false, false_or]
      have comparison :
          (potential buying probability factor amplitude fixedCost normalization rows selected remaining).evaluate.1.lessEqual
            (potential buying probability factor amplitude fixedCost normalization rows (v :: selected) remaining).evaluate.1 = true ↔
          ConditionalExpectation.potential buying probability factor amplitude fixedCost normalization selected remaining ≤
            ConditionalExpectation.potential buying probability factor amplitude fixedCost normalization (v :: selected) remaining := by
        rw [Code.lessEqual_correct, Expr.evaluate_value, Expr.evaluate_value,
          potential_eq_mathematical buying probability factor amplitude fixedCost normalization rows nodup complete,
          potential_eq_mathematical buying probability factor amplitude fixedCost normalization rows nodup complete]
      split
      · rename_i first
        rw [if_pos (comparison.mp first)]
        exact ih selected
      · rename_i second
        rw [if_neg (fun h => second (comparison.mpr h))]
        exact ih (v :: selected)

theorem chooseScheduled_work (buying probability : V → ℚ) (factor : R → V → ℚ)
    (amplitude : R → ℚ) (fixedCost normalization : ℚ) (rows : List R) (selected remaining : List V) :
    (chooseScheduled buying probability factor amplitude fixedCost normalization rows selected remaining).2 ≤
      remaining.length * (24 * (rows.length + 1) * (selected.length + remaining.length + 1) + 2) := by
  induction remaining generalizing selected with
  | nil => simp [chooseScheduled]
  | cons v remaining ih =>
    have left := potential_size_bound buying probability factor amplitude fixedCost normalization rows selected remaining
    have right := potential_size_bound buying probability factor amplitude fixedCost normalization rows (v :: selected) remaining
    have ih_left := ih selected
    have ih_right := ih (v :: selected)
    simp only [List.length_cons] at right ih_right ⊢
    simp only [chooseScheduled]
    split
    · dsimp only
      nlinarith only [ih_left, Nat.zero_le (rows.length * remaining.length), Nat.zero_le remaining.length,
        Nat.zero_le (rows.length * selected.length), Nat.zero_le selected.length, Nat.zero_le rows.length]
    · simp only [Expr.evaluate_count]
      split
      · nlinarith only [ih_left, left, right, Nat.zero_le (rows.length * remaining.length),
          Nat.zero_le remaining.length, Nat.zero_le (rows.length * selected.length),
          Nat.zero_le selected.length, Nat.zero_le rows.length]
      · nlinarith only [ih_right, left, right, Nat.zero_le (rows.length * remaining.length),
          Nat.zero_le remaining.length, Nat.zero_le (rows.length * selected.length),
          Nat.zero_le selected.length, Nat.zero_le rows.length]

end BuyAtBulk.Computation.HelperExpressions
