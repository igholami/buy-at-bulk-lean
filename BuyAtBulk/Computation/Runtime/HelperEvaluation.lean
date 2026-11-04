import BuyAtBulk.Computation.Runtime.Expression

/-! Arithmetic-evaluation part of conditional-expectation selection.
The coefficient tables and expression construction are separate obligations.
This trace charges every repeated tree evaluation and all comparison products;
no conclusion about untraced coefficient callbacks is asserted. -/
namespace BuyAtBulk.Computation.Runtime.HelperEvaluation
open Rational RawExpression
variable {V R : Type}

/-- Fixed numerical tables, already constructed by the coefficient phase. -/
structure Tables (V R : Type) where
  buying : V → ℚ
  probability : V → ℚ
  factor : R → V → ℚ
  amplitude : R → ℚ
  fixedCost : ℚ
  normalization : ℚ
  rows : List R

def potential (tables : Tables V R) (selected remaining : List V) : Expr :=
  HelperExpressions.potential tables.buying tables.probability tables.factor tables.amplitude
    tables.fixedCost tables.normalization tables.rows selected remaining

def probabilityEvents (p : ℚ) : List Event :=
  [event .dispatch [0], event .read [p.num, p.den], event .equal [p.num, 0],
    event .branch [if p = 0 then 1 else 0]]

def choose (tables : Tables V R) : List V → List V → Result (List V)
  | selected, [] => ⟨selected, []⟩
  | selected, v :: remaining =>
    if zero : tables.probability v = 0 then
      let rest := choose tables selected remaining
      ⟨rest.value, probabilityEvents (tables.probability v) ++ rest.events⟩
    else
      let left := RawExpression.evaluate (potential tables selected remaining)
      let right := RawExpression.evaluate (potential tables (v :: selected) remaining)
      let comparison := RawExpression.lessEqual left.value right.value
      let rest := if comparison.value then choose tables selected remaining
        else choose tables (v :: selected) remaining
      ⟨rest.value, probabilityEvents (tables.probability v) ++ left.events ++ right.events ++
        comparison.events ++ [event .branch [if comparison.value then 1 else 0]] ++ rest.events⟩
termination_by _ remaining => remaining.length

def original (tables : Tables V R) (selected remaining : List V) : List V × ℕ :=
  HelperExpressions.chooseScheduled tables.buying tables.probability tables.factor tables.amplitude
    tables.fixedCost tables.normalization tables.rows selected remaining

theorem choose_value (tables : Tables V R) (selected remaining : List V) :
    (choose tables selected remaining).value = (original tables selected remaining).1 := by
  induction remaining generalizing selected with
  | nil => simp [choose, original, HelperExpressions.chooseScheduled]
  | cons v remaining ih =>
    simp only [choose, original, HelperExpressions.chooseScheduled]
    by_cases zero : tables.probability v = 0
    · simp only [zero, ↓reduceDIte, ↓reduceIte]
      exact ih selected
    · simp only [zero, ↓reduceDIte, ↓reduceIte, RawExpression.evaluate_value,
        RawExpression.lessEqual_value]
      simp only [potential] at *
      split_ifs <;> simp_all only [original, Bool.false_eq_true, ite_true, ite_false]

theorem choose_length (tables : Tables V R) (selected remaining : List V) :
    (choose tables selected remaining).events.length ≤ 10*(original tables selected remaining).2 := by
  induction remaining generalizing selected with
  | nil => simp [choose, original, HelperExpressions.chooseScheduled]
  | cons v remaining ih =>
    have left := RawExpression.evaluate_length (potential tables selected remaining)
    have right := RawExpression.evaluate_length (potential tables (v::selected) remaining)
    have ih_left := ih selected
    have ih_right := ih (v::selected)
    by_cases zero : tables.probability v = 0
    · simp only [choose, original, HelperExpressions.chooseScheduled, zero, ↓reduceDIte, ↓reduceIte,
        List.length_append, probabilityEvents, List.length_cons, List.length_nil]
      dsimp [original] at ih_left
      omega
    · simp only [choose, original, HelperExpressions.chooseScheduled, zero, ↓reduceDIte, ↓reduceIte,
        List.length_append, probabilityEvents, List.length_cons, List.length_nil,
        RawExpression.lessEqual_length, RawExpression.evaluate_value, RawExpression.lessEqual_value]
      dsimp [original] at ih_left ih_right
      simp only [Expr.evaluate_count]
      simp only [potential] at left right ⊢
      split_ifs <;> simp_all only [Bool.false_eq_true, ite_true, ite_false] <;> omega

theorem choose_polynomial (tables : Tables V R) (selected remaining : List V) :
    (choose tables selected remaining).events.length ≤
      10*(remaining.length*(24*(tables.rows.length+1)*(selected.length+remaining.length+1)+2)) := by
  exact (choose_length tables selected remaining).trans
    (Nat.mul_le_mul_left 10 (HelperExpressions.chooseScheduled_work tables.buying tables.probability tables.factor
      tables.amplitude tables.fixedCost tables.normalization tables.rows selected remaining))

structure CoefficientsBounded (tables : Tables V R) (L : ℕ) : Prop where
  constants : 5 ≤ L
  buying : ∀ v, (Code.ofRat (tables.buying v)).bits+1 ≤ L
  probability : ∀ v, (Code.ofRat (tables.probability v)).bits+1 ≤ L
  factor : ∀ r ∈ tables.rows, ∀ v, (Code.ofRat (tables.factor r v)).bits+1 ≤ L
  amplitude : ∀ r ∈ tables.rows, (Code.ofRat (tables.amplitude r)).bits+1 ≤ L
  fixedCost : (Code.ofRat tables.fixedCost).bits+1 ≤ L
  normalization : (Code.ofRat tables.normalization).bits+1 ≤ L

theorem potential_leaves (tables : Tables V R) (L : ℕ) (bound : CoefficientsBounded tables L)
    (selected remaining : List V) : (potential tables selected remaining).maxLeafBudget ≤ L := by
  have zero : (HelperExpressions.atom 0).maxLeafBudget ≤ L :=
    (by decide : (HelperExpressions.atom 0).maxLeafBudget ≤ 5).trans bound.constants
  have one : (HelperExpressions.atom 1).maxLeafBudget ≤ L :=
    (by decide : (HelperExpressions.atom 1).maxLeafBudget ≤ 5).trans bound.constants
  have selected_buying : (HelperExpressions.sum (selected.map fun v => HelperExpressions.atom (tables.buying v))).maxLeafBudget ≤ L := by
    apply HelperExpressions.sum_leaf_bound _ L zero
    intro e member
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp member
    exact bound.buying v
  have remaining_buying : (HelperExpressions.sum (remaining.map fun v =>
      Expr.mul (HelperExpressions.atom (tables.probability v)) (HelperExpressions.atom (tables.buying v)))).maxLeafBudget ≤ L := by
    apply HelperExpressions.sum_leaf_bound _ L zero
    intro e member
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp member
    exact max_le (bound.probability v) (bound.buying v)
  have row_bound : ∀ r ∈ tables.rows,
      (HelperExpressions.row tables.probability (tables.factor r) (tables.amplitude r) selected remaining).maxLeafBudget ≤ L := by
    intro r member
    apply max_le
    · apply max_le (bound.amplitude r member)
      apply HelperExpressions.product_leaf_bound _ L one
      intro e present
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp present
      exact bound.factor r member v
    · apply HelperExpressions.product_leaf_bound _ L one
      intro e present
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp present
      exact max_le (max_le one (bound.probability v))
        (max_le (bound.probability v) (bound.factor r member v))
  apply max_le
  · exact max_le (max_le (max_le bound.fixedCost selected_buying) remaining_buying) bound.normalization
  · apply HelperExpressions.sum_leaf_bound _ L zero
    intro e member
    obtain ⟨r, present, rfl⟩ := List.mem_map.mp member
    exact row_bound r present

theorem probability_bounded (p : ℚ) (L : ℕ)
    (input : (Code.ofRat p).bits+1 ≤ L) : EventsBounded (probabilityEvents p) (L+3) := by
  have bound := Code.bounded_mono (Code.ofRat p).bounded_of_bits (show (Code.ofRat p).bits+1 ≤ L+3 by omega)
  have zero : (0 : ℕ) < 2^(L+3) := by positivity
  have one : (1 : ℕ) < 2^(L+3) := Nat.one_lt_pow (by omega) (by decide)
  have denominator : p.den < 2^(L+3) := by simpa only [Code.ofRat, Int.natAbs_natCast] using bound.2
  by_cases condition : p = 0 <;>
    simp [EventsBounded, probabilityEvents, event, condition, zero, one,
      show p.num.natAbs < 2^(L+3) from bound.1,
      denominator]

theorem choose_bounded (tables : Tables V R) (L N : ℕ) (bound : CoefficientsBounded tables L)
    (selected remaining : List V) (size : selected.length+remaining.length+1 ≤ N) :
    EventsBounded (choose tables selected remaining).events
      (24*(tables.rows.length+1)*N*L+5) := by
  have positive : 0 < L := by have := bound.constants; omega
  induction remaining generalizing selected with
  | nil => simp [choose, EventsBounded]
  | cons v remaining ih =>
    have Npos : 1 ≤ N := by simp only [List.length_cons] at size; omega
    have scale : 1 ≤ 24*(tables.rows.length+1)*N := by nlinarith
    have probability := events_mono (probability_bounded (tables.probability v) L (bound.probability v))
      (show L+3 ≤ 24*(tables.rows.length+1)*N*L+5 by nlinarith)
    have small_left : (potential tables selected remaining).budget ≤ 12*(tables.rows.length+1)*N*L := by
      apply ((potential tables selected remaining).budget_le_size_mul L positive (potential_leaves tables L bound selected remaining)).trans
      apply Nat.mul_le_mul_right L
      exact (HelperExpressions.potential_size_bound tables.buying tables.probability tables.factor tables.amplitude
        tables.fixedCost tables.normalization tables.rows selected remaining).trans
          (Nat.mul_le_mul_left _ (by simp only [List.length_cons] at size; omega))
    have small_right : (potential tables (v::selected) remaining).budget ≤ 12*(tables.rows.length+1)*N*L := by
      apply ((potential tables (v::selected) remaining).budget_le_size_mul L positive
        (potential_leaves tables L bound (v::selected) remaining)).trans
      apply Nat.mul_le_mul_right L
      exact (HelperExpressions.potential_size_bound tables.buying tables.probability tables.factor tables.amplitude
        tables.fixedCost tables.normalization tables.rows (v::selected) remaining).trans
          (Nat.mul_le_mul_left _ (by simp only [List.length_cons] at size ⊢; omega))
    have left := events_mono (RawExpression.evaluate_bounded (potential tables selected remaining))
      (show (potential tables selected remaining).budget+3 ≤ 24*(tables.rows.length+1)*N*L+5 by nlinarith)
    have right := events_mono (RawExpression.evaluate_bounded (potential tables (v::selected) remaining))
      (show (potential tables (v::selected) remaining).budget+3 ≤ 24*(tables.rows.length+1)*N*L+5 by nlinarith)
    have comparison := events_mono (RawExpression.lessEqual_bounded
      (potential tables selected remaining).evaluate_bounded
      (potential tables (v::selected) remaining).evaluate_bounded)
      (show (potential tables selected remaining).budget+(potential tables (v::selected) remaining).budget+3 ≤
        24*(tables.rows.length+1)*N*L+5 by nlinarith)
    have tail_left := ih selected (by simp only [List.length_cons] at size; omega)
    have tail_right := ih (v::selected) (by simp only [List.length_cons] at size ⊢; omega)
    by_cases zero : tables.probability v = 0
    · simp only [choose, zero, ↓reduceDIte, ↓reduceIte]
      exact events_append.mpr ⟨by simpa only [zero] using probability, tail_left⟩
    · simp only [choose, zero, ↓reduceDIte, ↓reduceIte, RawExpression.evaluate_value]
      apply events_append.mpr
      constructor
      · apply events_append.mpr
        constructor
        · exact events_append.mpr ⟨events_append.mpr ⟨events_append.mpr ⟨probability, left⟩, right⟩, comparison⟩
        · have one : (1 : ℕ) < 2^(24*(tables.rows.length+1)*N*L+5) := Nat.one_lt_pow (by omega) (by decide)
          have zero : (0 : ℕ) < 2^(24*(tables.rows.length+1)*N*L+5) := by positivity
          apply events_single.mpr
          intro z member
          have equal : z = (if (RawExpression.lessEqual (potential tables selected remaining).evaluate.1
            (potential tables (v::selected) remaining).evaluate.1).value then 1 else 0) := by simpa [event] using member
          rw [equal]
          split_ifs <;> simpa using (by first | exact one | exact zero)
      · split_ifs
        · exact tail_left
        · exact tail_right

private theorem width_append {a b : List Event} :
    EventsWidth (a ++ b) 3 ↔ EventsWidth a 3 ∧ EventsWidth b 3 := by
  constructor
  · intro bound
    exact ⟨fun entry member => bound entry (List.mem_append_left _ member),
      fun entry member => bound entry (List.mem_append_right _ member)⟩
  · rintro ⟨left, right⟩ entry member
    rcases List.mem_append.mp member with member | member
    · exact left entry member
    · exact right entry member

private theorem probability_width (p : ℚ) : EventsWidth (probabilityEvents p) 3 := by
  simp [EventsWidth, probabilityEvents, event]

theorem choose_width (tables : Tables V R) (selected remaining : List V) :
    EventsWidth (choose tables selected remaining).events 3 := by
  induction remaining generalizing selected with
  | nil => simp [choose, EventsWidth]
  | cons v remaining ih =>
    by_cases zero : tables.probability v = 0
    · simp only [choose, zero, ↓reduceDIte, ↓reduceIte]
      exact width_append.mpr ⟨probability_width _, ih selected⟩
    · simp only [choose, zero, ↓reduceDIte, ↓reduceIte]
      apply width_append.mpr
      constructor
      · apply width_append.mpr
        constructor
        · exact width_append.mpr ⟨width_append.mpr ⟨width_append.mpr
            ⟨probability_width _, RawExpression.evaluate_width _⟩, RawExpression.evaluate_width _⟩,
              RawExpression.lessEqual_width _ _⟩
        · simp [EventsWidth, event]
      · split_ifs <;> exact ih _

/-- This is the evaluation-stage charge only. Coefficient creation, syntax
construction, selected-list construction and table allocation are additional. -/
theorem choose_bitWork (tables : Tables V R) (L : ℕ) (bound : CoefficientsBounded tables L)
    (selected remaining : List V) :
    bitWork (choose tables selected remaining).events ≤
      (10*(remaining.length*(24*(tables.rows.length+1)*(selected.length+remaining.length+1)+2))) *
      (3*(24*(tables.rows.length+1)*(selected.length+remaining.length+1)*L+6)+1)^2 := by
  have words : ∀ entry ∈ (choose tables selected remaining).events, ∀ z ∈ entry.values,
      z.natAbs.size+1 ≤ 24*(tables.rows.length+1)*(selected.length+remaining.length+1)*L+6 := by
    intro entry member z value
    have bound := choose_bounded tables L (selected.length+remaining.length+1) bound selected remaining le_rfl
    have bits := Nat.size_le.mpr (bound entry member z value)
    omega
  exact (RawExpression.bitWork_bound _ 3 _ (choose_width tables selected remaining) words).trans
    (Nat.mul_le_mul_right _ (choose_polynomial tables selected remaining))

end BuyAtBulk.Computation.Runtime.HelperEvaluation
