import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-! Finite disjoint-support accounting used for heavy and light birth rows.
Graph separation is proved separately from actual no-near-center birth guards. -/
namespace BuyAtBulk.Packing

variable {I V : Type} [DecidableEq I]

theorem one_positive_sum_le (indices : Finset I) (value : I → ℚ) (budget : ℚ)
    (nonneg : ∀ i ∈ indices, 0 ≤ value i) (bounded : ∀ i ∈ indices, value i ≤ budget)
    (budget_nonneg : 0 ≤ budget)
    (separated : ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j → ¬ (0 < value i ∧ 0 < value j)) :
    (∑ i ∈ indices, value i) ≤ budget := by
  by_cases positive : ∃ i ∈ indices, 0 < value i
  · obtain ⟨i, hi, hp⟩ := positive
    have zero : ∀ j ∈ indices, j ≠ i → value j = 0 := by
      intro j hj hji
      have hn : ¬ 0 < value j := fun hpos => separated i hi j hj (Ne.symm hji) ⟨hp, hpos⟩
      exact le_antisymm (not_lt.mp hn) (nonneg j hj)
    rw [Finset.sum_eq_single i (fun j hj hji => zero j hj hji) (fun hn => False.elim (hn hi))]
    exact bounded i hi
  · have zero : ∀ i ∈ indices, value i = 0 := by
      intro i hi
      apply le_antisymm
      · by_contra hn
        exact positive ⟨i, hi, lt_of_not_ge hn⟩
      · exact nonneg i hi
    rw [Finset.sum_eq_zero zero]
    exact budget_nonneg

theorem separated_rows_sum_le (indices : Finset I) (nodes : Finset V)
    (toll : I → V → ℚ) (weight buying : V → ℚ)
    (weight_nonneg : ∀ v ∈ nodes, 0 ≤ weight v) (buying_nonneg : ∀ v ∈ nodes, 0 ≤ buying v)
    (nonneg : ∀ i ∈ indices, ∀ v ∈ nodes, 0 ≤ toll i v)
    (bounded : ∀ i ∈ indices, ∀ v ∈ nodes, toll i v ≤ buying v)
    (separated : ∀ v ∈ nodes, ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j →
      ¬ (0 < toll i v ∧ 0 < toll j v)) :
    (∑ i ∈ indices, ∑ v ∈ nodes, weight v * toll i v) ≤
      ∑ v ∈ nodes, weight v * buying v := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro v hv
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (one_positive_sum_le indices (fun i => toll i v) (buying v)
    (fun i hi => nonneg i hi v hv) (fun i hi => bounded i hi v hv) (buying_nonneg v hv)
    (separated v hv)) (weight_nonneg v hv)

end BuyAtBulk.Packing
