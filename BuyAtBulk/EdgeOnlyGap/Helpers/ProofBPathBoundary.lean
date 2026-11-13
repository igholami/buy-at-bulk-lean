import BuyAtBulk.Model.GraphInstance
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap.ProofB
attribute [local instance] Classical.propDecidable

/-- In characteristic two the internal vertices of a walk cancel in pairs. -/
theorem walkBoundary {V : Type} [DecidableEq V] {G : SimpleGraph V} {s t : V}
    (P : G.Walk s t) (v : V) :
    (P.edges.map fun e => if v ∈ e then (1 : ZMod 2) else 0).sum =
      (if v = s then 1 else 0) + (if v = t then 1 else 0) := by
  classical
  induction P with
  | @nil u => by_cases h : v = u <;> simp [h] <;> norm_num <;> decide
  | @cons s u t h P ih =>
    have hsu : s ≠ u := h.ne
    simp only [SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons, ih,
      Sym2.mem_iff]
    by_cases hs : v = s <;> by_cases hu : v = u <;> by_cases ht : v = t <;>
      simp_all <;> norm_num <;> decide

/-- The finite edge-set boundary of a simple path is precisely its endpoints. -/
theorem pathBoundary {V : Type} [DecidableEq V] {G : SimpleGraph V} {s t : V}
    (P : G.Path s t) (v : V) :
    (∑ e ∈ P.val.edges.toFinset, if v ∈ e then (1 : ZMod 2) else 0) =
      (if v = s then 1 else 0) + (if v = t then 1 else 0) := by
  classical
  rw [List.sum_toFinset _ P.property.isTrail.edges_nodup]
  exact walkBoundary P.val v

end BuyAtBulk.EdgeOnlyGap.ProofB
