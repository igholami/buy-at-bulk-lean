import BuyAtBulk.Computation.Rounding.Algorithm
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! Cost accounting for the actual indexed output path list. The index
permutation proves that every request is charged exactly once. -/
namespace BuyAtBulk.Computation.Rounding
open BuyAtBulk.UpperBound
variable {V : Type} [Fintype V] [DecidableEq V] {h : ℕ} {G : SimpleGraph V}

def rentalCost (physical : V → ℚ) (demand : Fin h → ℚ)
    {source target : Fin h → V} (entries : List (Batch.RouteEntry G source target)) : ℚ :=
  (entries.map fun entry => demand entry.1 * Attachment.pathCost G physical entry.2).sum

theorem rentalCost_eq (physical : V → ℚ) (demand : Fin h → ℚ)
    {source target : Fin h → V} (entries : List (Batch.RouteEntry G source target)) :
    rentalCost physical demand entries =
      (entries.map fun entry => demand entry.1 * NodeMetric.walkWeight G physical entry.2.val).sum := by
  simp only [rentalCost, Attachment.pathCost_eq]

theorem indexed_sum (weight : Fin h → ℚ) {source target : Fin h → V}
    (entries : List (Batch.RouteEntry G source target))
    (indices : (entries.map fun entry => entry.1).Perm (List.finRange h)) :
    (entries.map fun entry => weight entry.1).sum = ∑ i, weight i := by
  have permuted := (indices.map weight).sum_eq
  simpa only [List.map_map, Function.comp_def, ← Fin.sum_univ_def] using permuted

theorem rentalCost_le (physical : V → ℚ) (demand lengths : Fin h → ℚ)
    (demand_nonneg : ∀ i, 0 ≤ demand i) {source target : Fin h → V}
    (entries : List (Batch.RouteEntry G source target))
    (indices : (entries.map fun entry => entry.1).Perm (List.finRange h)) (coefficient : ℚ)
    (bounded : ∀ entry ∈ entries, NodeMetric.walkWeight G physical entry.2.val ≤ coefficient * lengths entry.1) :
    rentalCost physical demand entries ≤ coefficient * ∑ i, demand i * lengths i := by
  rw [rentalCost_eq]
  have bounds : ∀ entry ∈ entries,
      demand entry.1 * NodeMetric.walkWeight G physical entry.2.val ≤ coefficient * (demand entry.1 * lengths entry.1) := by
    intro entry member
    exact (mul_le_mul_of_nonneg_left (bounded entry member) (demand_nonneg entry.1)).trans_eq (by ring)
  have scaled : (entries.map fun entry => coefficient * (demand entry.1 * lengths entry.1)).sum =
      coefficient * (entries.map fun entry => demand entry.1 * lengths entry.1).sum := by
    clear indices bounded bounds
    induction entries with
    | nil => simp
    | cons entry entries ih => simp only [List.map_cons, List.sum_cons, ih, mul_add]
  calc
    _ ≤ _ := List.sum_le_sum bounds
    _ = _ := scaled
    _ = _ := by rw [indexed_sum (fun i => demand i * lengths i) entries indices]

theorem phase_orders_perm (lengths : Fin h → ℚ) (ratio : ℕ) :
    (CoreRun.requestOrder (zeroActive lengths) (fun _ => 1) ++
      CoreRun.requestOrder (positiveActive lengths) (allowance lengths)).Perm (List.finRange h) := by
  have nodup : (CoreRun.requestOrder (zeroActive lengths) (fun _ => 1) ++
      CoreRun.requestOrder (positiveActive lengths) (allowance lengths)).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨CoreRun.requestOrder_nodup _ _, CoreRun.requestOrder_nodup _ _, ?_⟩
    intro i zero j positive equal
    subst j
    have hz : lengths i = 0 := by simpa only [CoreRun.mem_requestOrder, zeroActive, Finset.mem_filter, Finset.mem_univ, true_and] using zero
    have hp : lengths i ≠ 0 := by simpa only [CoreRun.mem_requestOrder, positiveActive, Finset.mem_filter, Finset.mem_univ, true_and] using positive
    exact hp hz
  apply (List.perm_ext_iff_of_nodup nodup (List.nodup_finRange h)).mpr
  intro i
  simp only [List.mem_append, CoreRun.mem_requestOrder, zeroActive, positiveActive,
    Finset.mem_filter, Finset.mem_univ, true_and, List.mem_finRange, iff_true]
  exact em (lengths i = 0)

end BuyAtBulk.Computation.Rounding
