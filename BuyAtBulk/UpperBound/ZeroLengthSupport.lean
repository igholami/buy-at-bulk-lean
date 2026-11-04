import BuyAtBulk.UpperBound.NodeLP
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-! Exact zero-rental support facts: nonnegative physical lengths never vanish
merely because a resource has been bought. Zero flow-length forces every used
node of each positive-flow simple path to have physical length zero. -/
noncomputable section
namespace BuyAtBulk.UpperBound.NodeLP

variable {V : Type} [Fintype V] {G : SimpleGraph V} {h : ℕ}
local instance zeroLengthSupportLocalInst1 : DecidableEq V := Classical.decEq V
local instance zeroLengthSupportLocalInst2 : DecidableRel G.Adj := Classical.decRel _
variable (lp : NodeLP G h)

theorem positive_path_zero_length (i : Fin h) (zero_length : lp.fractionalLength i = 0)
    (path : G.Path (lp.source i) (lp.target i)) (positive : 0 < lp.flow i path) :
    NodeMetric.walkWeight G lp.physical path.val = 0 := by
  have nonneg : ∀ p : G.Path (lp.source i) (lp.target i),
      0 ≤ NodeMetric.walkWeight G lp.physical p.val * lp.flow i p := by
    intro p
    apply mul_nonneg
    · exact Finset.sum_nonneg fun v _ => lp.physical_nonneg v
    · exact lp.flow_nonneg i p
  have term_zero : NodeMetric.walkWeight G lp.physical path.val * lp.flow i path = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => nonneg p)).mp zero_length path (Finset.mem_univ path)
  exact (mul_eq_zero.mp term_zero).resolve_right (ne_of_gt positive)

theorem positive_path_zero_nodes (i : Fin h) (zero_length : lp.fractionalLength i = 0)
    (path : G.Path (lp.source i) (lp.target i)) (positive : 0 < lp.flow i path) :
    ∀ v ∈ path.val.support, lp.physical v = 0 := by
  have zero := lp.positive_path_zero_length i zero_length path positive
  intro v hv
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => lp.physical_nonneg a)).mp zero v (List.mem_toFinset.mpr hv)

theorem zero_rental_fractional_lengths (zero_rental : lp.rentalBudget = 0) (i : Fin h) :
    lp.fractionalLength i = 0 := by
  have nonneg : ∀ j, 0 ≤ lp.demand j * lp.fractionalLength j :=
    fun j => mul_nonneg (lp.demand_pos j).le (lp.fractionalLength_nonneg j)
  have zero : lp.demand i * lp.fractionalLength i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => nonneg j)).mp zero_rental i (Finset.mem_univ i)
  exact (mul_eq_zero.mp zero).resolve_left (ne_of_gt (lp.demand_pos i))

theorem exists_positive_flow_path (i : Fin h) : ∃ path, 0 < lp.flow i path := by
  by_contra hn
  push Not at hn
  have zero : ∀ path, lp.flow i path = 0 := fun path =>
    le_antisymm (hn path) (lp.flow_nonneg i path)
  have unit := lp.unit i
  simp [zero] at unit

end BuyAtBulk.UpperBound.NodeLP
