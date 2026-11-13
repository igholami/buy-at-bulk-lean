import BuyAtBulk.EdgeOnlyGap.Items.CollapseVertex
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBPathBoundary
import Mathlib.Algebra.CharP.Two

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap.ProofB
attribute [local instance] Classical.propDecidable

/-- Collapse commutes with the boundary of an individual non-loop edge. -/
theorem collapseEdgeBoundary {V W : Type} [Fintype V] [DecidableEq V] [DecidableEq W]
    (c : V → W) (x y : V) (hxy : x ≠ y) (v : W) (z : ZMod 2) :
    (∑ w : V, if c w = v then (if w ∈ s(x,y) then z else 0) else 0) =
      (if c x = v then z else 0) + (if c y = v then z else 0) := by
  classical
  have hpoint (w : V) :
      (if c w = v then (if w ∈ s(x,y) then z else 0) else 0) =
      (if w = x then (if c x = v then z else 0) else 0) +
      (if w = y then (if c y = v then z else 0) else 0) := by
    by_cases hx : w = x <;> by_cases hy : w = y <;>
      simp_all [Sym2.mem_iff]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp

end BuyAtBulk.EdgeOnlyGap.ProofB
