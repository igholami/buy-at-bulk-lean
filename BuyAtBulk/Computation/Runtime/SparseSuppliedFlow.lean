import BuyAtBulk.Computation.FlowDecomposition
import BuyAtBulk.Model.CompactFlowBottleneck

/-! Supplied weighted simple paths define a feasible unit directed transport
flow. These identities connect actual list aggregation to decomposition. -/
namespace BuyAtBulk.Computation.Runtime.SparseSupplied
open BuyAtBulk.CompactFlow
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

 theorem path_transport_le_one {s t : V} (p : G.Path s t) (u v : V) :
    transportVisits p.val u v ≤ 1 := by
  classical
  by_cases ha : G.Adj u v
  · have h := path_transportVisits_dart p ⟨(u,v),ha⟩
    change transportVisits p.val u v = _ at h
    rw [h]
    split_ifs <;> norm_num
  · rw [transportVisits_nonedge p.val u v ha]
    norm_num

 theorem aggregate_nonneg {s t : V} (entries : FlowDecomposition.WeightedPaths G s t)
    (nonneg : ∀ e ∈ entries, 0 ≤ e.1) (u v : V) :
    0 ≤ (entries.map fun e => e.1 * transportVisits e.2.val u v).sum := by
  apply List.sum_nonneg
  intro q mem
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp mem
  exact mul_nonneg (nonneg e he) (transportVisits_nonneg e.2.val u v)

 theorem aggregate_nonedge {s t : V} (entries : FlowDecomposition.WeightedPaths G s t)
    (u v : V) (nonedge : ¬G.Adj u v) :
    (entries.map fun e => e.1 * transportVisits e.2.val u v).sum = 0 := by
  simp [transportVisits_nonedge _ u v nonedge]

 theorem aggregate_le_mass {s t : V} (entries : FlowDecomposition.WeightedPaths G s t)
    (nonneg : ∀ e ∈ entries, 0 ≤ e.1) (u v : V) :
    (entries.map fun e => e.1 * transportVisits e.2.val u v).sum ≤
      (entries.map Prod.fst).sum := by
  induction entries with
  | nil => simp
  | cons e rest ih =>
    simp only [List.map_cons,List.sum_cons]
    have first : e.1 * transportVisits e.2.val u v ≤ e.1 := by
      simpa using (mul_le_mul_of_nonneg_left (path_transport_le_one e.2 u v) (nonneg e (by simp)))
    exact add_le_add first (ih (fun x hx => nonneg x (by simp [hx])))

 theorem aggregate_le_one {s t : V} (entries : FlowDecomposition.WeightedPaths G s t)
    (nonneg : ∀ e ∈ entries, 0 ≤ e.1) (unit : (entries.map Prod.fst).sum = 1)
    (u v : V) : (entries.map fun e => e.1 * transportVisits e.2.val u v).sum ≤ 1 := by
  simpa [unit] using aggregate_le_mass entries nonneg u v

 theorem aggregate_balance_mass {s t : V} (entries : FlowDecomposition.WeightedPaths G s t)
    (v : V) :
    (∑ u, (entries.map fun e => e.1 * transportVisits e.2.val v u).sum) -
      (∑ u, (entries.map fun e => e.1 * transportVisits e.2.val u v).sum) =
      (entries.map Prod.fst).sum * ((if s = v then 1 else 0) - (if t = v then 1 else 0)) := by
  classical
  induction entries with
  | nil => simp
  | cons e rest ih =>
    simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib]
    have balance : (∑ u, transportVisits e.2.val v u) -
        (∑ u, transportVisits e.2.val u v) =
        (if s = v then 1 else 0) - (if t = v then 1 else 0) := by
      have ho := visits_outgoing e.2.val v
      have hi := visits_incoming e.2.val v
      by_cases hs : s = v <;> by_cases ht : t = v <;> simp_all <;> linarith
    simp only [← Finset.mul_sum]
    calc
      _ = e.1 * ((∑ u, transportVisits e.2.val v u) - (∑ u, transportVisits e.2.val u v)) +
          ((∑ u, (rest.map fun e => e.1 * transportVisits e.2.val v u).sum) -
          (∑ u, (rest.map fun e => e.1 * transportVisits e.2.val u v).sum)) := by ring
      _ = _ := by rw [balance,ih]; ring

 theorem aggregate_balance {s t : V} (entries : FlowDecomposition.WeightedPaths G s t)
    (unit : (entries.map Prod.fst).sum = 1) (v : V) :
    (∑ u, (entries.map fun e => e.1 * transportVisits e.2.val v u).sum) -
      (∑ u, (entries.map fun e => e.1 * transportVisits e.2.val u v).sum) =
      (if s = v then 1 else 0) - (if t = v then 1 else 0) := by
  simpa [unit] using aggregate_balance_mass entries v

end BuyAtBulk.Computation.Runtime.SparseSupplied
