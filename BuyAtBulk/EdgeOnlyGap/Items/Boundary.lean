import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import BuyAtBulk.EdgeOnlyGap.Items.CycleRank

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 4: binary edge chains and boundary; also. -/
def boundary (H : FiniteGraph) (W : Finset (Edges H)) :
    ({e // e ∈ W} → ZMod 2) →ₗ[ZMod 2] (Fin H.n → ZMod 2) where
  toFun := fun z v => ∑ e, if v=e.val.val.1 ∨ v=e.val.val.2 then z e else 0
  map_add' := by
    intro x y
    ext v
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    split_ifs <;> simp
  map_smul' := by
    intro c x
    ext v
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    split_ifs <;> simp

end BuyAtBulk.EdgeOnlyGap
