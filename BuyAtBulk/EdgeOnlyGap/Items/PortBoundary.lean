import Mathlib.LinearAlgebra.Pi

import BuyAtBulk.EdgeOnlyGap.Items.UsedChains

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 4: boundary at copy vertices only, hubs unrestricted. -/
def portBoundary (H : FiniteGraph) (q d : ℕ) (π : Lift H q) (hd : 0 < d)
    (r : (supplyData H q d π hd).toInstance.IntegralRouting) :
    UsedChains H q d π hd r →ₗ[ZMod 2] ((Fin H.n × Fin q) → ZMod 2) where
  toFun := fun z v => ∑ a, if ∃ e, (supplyData H q d π hd).location a.val = Sum.inr e ∧
    Sum.inr v ∈ e then z a else 0
  map_add' := by
    intro x y
    ext v
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp
  map_smul' := by
    intro c x
    ext v
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp

end BuyAtBulk.EdgeOnlyGap
