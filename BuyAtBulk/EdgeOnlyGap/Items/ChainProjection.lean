import Mathlib.LinearAlgebra.Pi

import BuyAtBulk.EdgeOnlyGap.Items.UsedChains

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 4: core edges project to base edges, spokes to zero. -/
def chainProjection (H : FiniteGraph) (q d : ℕ) (π : Lift H q) (hd : 0 < d)
    (r : (supplyData H q d π hd).toInstance.IntegralRouting) :
    UsedChains H q d π hd r →ₗ[ZMod 2] (Edges H → ZMod 2) where
  toFun := fun z e => ∑ a,
    if ∃ j k : Fin q, (supplyData H q d π hd).location a.val =
      Sum.inr (s(Sum.inr (e.val.1,j),Sum.inr (e.val.2,k))) then z a else 0
  map_add' := by
    intro x y
    ext e
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp
  map_smul' := by
    intro c x
    ext e
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp

end BuyAtBulk.EdgeOnlyGap
