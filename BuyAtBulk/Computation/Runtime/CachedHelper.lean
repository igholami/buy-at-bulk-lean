import BuyAtBulk.Computation.Runtime.HelperConstruction

/-! Actual cached-table helper evaluator, including syntax construction,
repeated arithmetic evaluation, signed comparison, selection-list allocation
and probability/address reads. Coefficient-table materialization is separate. -/
set_option maxHeartbeats 1600000
namespace BuyAtBulk.Computation.Runtime.CachedHelper
open Rational RawExpression
open HelperConstruction (StoredTables)
variable {n m : ℕ}

def choose (stored : StoredTables n m) : List (Fin n) → List (Fin n) → Result (List (Fin n))
  | selected, [] => ⟨selected, [event .dispatch [0]]⟩
  | selected, v::remaining =>
    let probability := stored.probability[v.val]
    let controlEvents := [event .read [v.val]] ++ HelperEvaluation.probabilityEvents probability
    if probability = 0 then
      let rest := choose stored selected remaining
      ⟨rest.value, controlEvents ++ rest.events⟩
    else
      let leftSyntax := HelperConstruction.potential stored selected remaining
      let left := RawExpression.evaluate leftSyntax.value
      let nextSelected := v::selected
      let rightSyntax := HelperConstruction.potential stored nextSelected remaining
      let right := RawExpression.evaluate rightSyntax.value
      let comparison := RawExpression.lessEqual left.value right.value
      let rest := if comparison.value then choose stored selected remaining else choose stored nextSelected remaining
      ⟨rest.value, controlEvents ++ leftSyntax.events ++ left.events ++ [event .pair [v.val]] ++
        rightSyntax.events ++ right.events ++ comparison.events ++
        [event .branch [if comparison.value then 1 else 0]] ++ rest.events⟩
termination_by _ remaining => remaining.length

theorem choose_value (stored : StoredTables n m) (selected remaining : List (Fin n)) :
    (choose stored selected remaining).value = (HelperEvaluation.original stored.tables selected remaining).1 := by
  induction remaining generalizing selected with
  | nil => simp [choose, HelperEvaluation.original, HelperExpressions.chooseScheduled]
  | cons v remaining ih =>
    simp only [choose, HelperEvaluation.original, HelperExpressions.chooseScheduled,
      HelperConstruction.potential_value, RawExpression.evaluate_value, RawExpression.lessEqual_value]
    simp only [StoredTables.tables, HelperEvaluation.original, HelperEvaluation.potential] at *
    by_cases zero : stored.probability[v.val] = 0
    · simp only [zero, ↓reduceIte]
      exact ih selected
    · simp only [zero, ↓reduceIte]
      split_ifs <;> simp_all only [Bool.false_eq_true, ite_true, ite_false]

theorem choose_count (stored : StoredTables n m) (selected remaining : List (Fin n)) :
    (choose stored selected remaining).events.length ≤
      14*(HelperEvaluation.original stored.tables selected remaining).2+1 := by
  induction remaining generalizing selected with
  | nil => simp [choose, HelperEvaluation.original, HelperExpressions.chooseScheduled]
  | cons v remaining ih =>
    have left_eval := RawExpression.evaluate_length (HelperEvaluation.potential stored.tables selected remaining)
    have right_eval := RawExpression.evaluate_length (HelperEvaluation.potential stored.tables (v::selected) remaining)
    have left_build := HelperConstruction.potential_cost stored selected remaining
    have right_build := HelperConstruction.potential_cost stored (v::selected) remaining
    rw [HelperConstruction.CostBound, HelperConstruction.potential_value] at left_build right_build
    have ih_left := ih selected
    have ih_right := ih (v::selected)
    simp only [HelperEvaluation.original] at ih_left ih_right
    simp only [choose, HelperEvaluation.original, HelperExpressions.chooseScheduled,
      HelperConstruction.potential_value, RawExpression.evaluate_value, RawExpression.lessEqual_value,
      List.length_append, HelperEvaluation.probabilityEvents, List.length_cons, List.length_nil,
      RawExpression.lessEqual_length]
    simp only [StoredTables.tables, HelperEvaluation.potential] at left_build right_build left_eval right_eval ih_left ih_right ⊢
    by_cases zero : stored.probability[v.val] = 0
    · simp only [zero, ↓reduceIte, List.length_append, List.length_cons, List.length_nil]
      omega
    · simp only [zero, ↓reduceIte, Expr.evaluate_count]
      split_ifs <;> simp_all only [Bool.false_eq_true, ite_true, ite_false, List.length_append,
        List.length_cons, List.length_nil, RawExpression.lessEqual_length] <;> omega

theorem choose_polynomial (stored : StoredTables n m) (selected remaining : List (Fin n)) :
    (choose stored selected remaining).events.length ≤
      14*(remaining.length*(24*(m+1)*(selected.length+remaining.length+1)+2))+1 := by
  have base := HelperExpressions.chooseScheduled_work stored.tables.buying stored.tables.probability
    stored.tables.factor stored.tables.amplitude stored.tables.fixedCost stored.tables.normalization
    stored.tables.rows selected remaining
  have rows : stored.tables.rows.length = m := by simp [StoredTables.tables]
  rw [rows] at base
  exact (choose_count stored selected remaining).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 14 base) 1)

private theorem address_event (op : Operation) (v : Fin n) (K : ℕ) (large : n ≤ K) :
    EventsBounded [event op [(v.val : ℤ)]] K := by
  have index : (v.val : ℤ).natAbs < 2^K := by
    simp only [Int.natAbs_natCast]
    exact (v.isLt.trans Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_right (by decide) large)
  simpa [EventsBounded, event] using index

private theorem bit_event (b : ℤ) (op : Operation) (K : ℕ) (small : b = 0 ∨ b = 1) (large : 1 ≤ K) :
    EventsBounded [event op [b]] K := by
  have zero : (0 : ℕ) < 2^K := by positivity
  have one : (1 : ℕ) < 2^K := Nat.one_lt_pow (by omega) (by decide)
  rcases small with rfl | rfl <;> simp [EventsBounded, event, zero, one]

theorem choose_bounded (stored : StoredTables n m) (L N : ℕ)
    (coefficients : HelperEvaluation.CoefficientsBounded stored.tables L)
    (selected remaining : List (Fin n)) (size : selected.length+remaining.length+1 ≤ N) :
    EventsBounded (choose stored selected remaining).events
      (24*(m+1)*N*L+L+n+m+10) := by
  let K := 24*(m+1)*N*L+L+n+m+10
  have Kpos : 1 ≤ K := by dsimp [K]; omega
  have indices : n ≤ K := by dsimp [K]; omega
  have positive : 0 < L := by have := coefficients.constants; omega
  induction remaining generalizing selected with
  | nil => simpa only [choose] using bit_event 0 .dispatch K (Or.inl rfl) Kpos
  | cons v remaining ih =>
    have tail_left := ih selected (by simp only [List.length_cons] at size; omega)
    have tail_right := ih (v::selected) (by simp only [List.length_cons] at size ⊢; omega)
    have address := address_event .read v K indices
    have allocated := address_event .pair v K indices
    have probability := events_mono
      (HelperEvaluation.probability_bounded (stored.probability[v.val]) L (coefficients.probability v))
      (show L+3 ≤ K by dsimp [K]; omega)
    have build_left := events_mono (HelperConstruction.potential_bounded stored selected remaining L coefficients)
      (show L+n+m+5 ≤ K by dsimp [K]; omega)
    have build_right := events_mono (HelperConstruction.potential_bounded stored (v::selected) remaining L coefficients)
      (show L+n+m+5 ≤ K by dsimp [K]; omega)
    have small (a b : List (Fin n)) (short : a.length+b.length+1 ≤ N) :
        (HelperEvaluation.potential stored.tables a b).budget ≤ 12*(m+1)*N*L := by
      apply ((HelperEvaluation.potential stored.tables a b).budget_le_size_mul L positive
        (HelperEvaluation.potential_leaves stored.tables L coefficients a b)).trans
      apply Nat.mul_le_mul_right L
      have size_bound := HelperExpressions.potential_size_bound stored.tables.buying stored.tables.probability
        stored.tables.factor stored.tables.amplitude stored.tables.fixedCost stored.tables.normalization stored.tables.rows a b
      have rows : stored.tables.rows.length = m := by simp [StoredTables.tables]
      rw [rows] at size_bound
      exact size_bound.trans (Nat.mul_le_mul_left _ short)
    have small_left := small selected remaining (by simp only [List.length_cons] at size; omega)
    have small_right := small (v::selected) remaining (by simp only [List.length_cons] at size ⊢; omega)
    have evaluated_left := events_mono (RawExpression.evaluate_bounded (HelperEvaluation.potential stored.tables selected remaining))
      (show (HelperEvaluation.potential stored.tables selected remaining).budget+3 ≤ K by dsimp [K]; nlinarith)
    have evaluated_right := events_mono (RawExpression.evaluate_bounded (HelperEvaluation.potential stored.tables (v::selected) remaining))
      (show (HelperEvaluation.potential stored.tables (v::selected) remaining).budget+3 ≤ K by dsimp [K]; nlinarith)
    have comparison := events_mono (RawExpression.lessEqual_bounded
      (HelperEvaluation.potential stored.tables selected remaining).evaluate_bounded
      (HelperEvaluation.potential stored.tables (v::selected) remaining).evaluate_bounded)
      (show (HelperEvaluation.potential stored.tables selected remaining).budget+
        (HelperEvaluation.potential stored.tables (v::selected) remaining).budget+3 ≤ K by dsimp [K]; nlinarith)
    have branch_zero := bit_event 0 .branch K (Or.inl rfl) Kpos
    have branch_one := bit_event 1 .branch K (Or.inr rfl) Kpos
    by_cases zero : stored.probability[v.val] = 0
    · simp only [choose, zero, ↓reduceIte]
      exact events_append.mpr ⟨events_append.mpr ⟨address, by simpa only [zero] using probability⟩, tail_left⟩
    · simp only [choose, zero, ↓reduceIte, HelperConstruction.potential_value, RawExpression.evaluate_value]
      split_ifs <;> simp only [events_append] <;> repeat' apply And.intro
      all_goals first | assumption | exact tail_left | exact tail_right

end BuyAtBulk.Computation.Runtime.CachedHelper
