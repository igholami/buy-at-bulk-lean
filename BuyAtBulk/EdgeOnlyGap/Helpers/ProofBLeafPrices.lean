import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBLeafExtensionCode
import Mathlib.Tactic.Ring
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.EdgeOnlyGap.ProofB
open scoped BigOperators
attribute [local instance] Classical.propDecidable

@[simp] theorem leafOldBuying (D : BuyAtBulk.GraphData) (p : ℚ) (hp : 0 ≤ p) (a : Fin D.resourceCount) :
    (privateLeaves D p hp).buying (leafOldResource D p hp a) = D.buying a := by
  change (match (Fintype.equivFin (Fin D.resourceCount ⊕ (Fin D.requestCount × Bool))).symm
    (Fintype.equivFin _ (Sum.inl a)) with | Sum.inl j => D.buying j | Sum.inr _ => p) = _
  rw [Equiv.symm_apply_apply]
@[simp] theorem leafOldLength (D : BuyAtBulk.GraphData) (p : ℚ) (hp : 0 ≤ p) (a : Fin D.resourceCount) :
    (privateLeaves D p hp).length (leafOldResource D p hp a) = D.length a := by
  change (match (Fintype.equivFin (Fin D.resourceCount ⊕ (Fin D.requestCount × Bool))).symm
    (Fintype.equivFin _ (Sum.inl a)) with | Sum.inl j => D.length j | Sum.inr _ => p) = _
  rw [Equiv.symm_apply_apply]
@[simp] theorem leafPendantBuying (D : BuyAtBulk.GraphData) (p : ℚ) (hp : 0 ≤ p)
    (j : Fin D.requestCount) (b : Bool) :
    (privateLeaves D p hp).buying (leafPendantResource D p hp j b) = p := by
  change (match (Fintype.equivFin (Fin D.resourceCount ⊕ (Fin D.requestCount × Bool))).symm
    (Fintype.equivFin _ (Sum.inr (j,b))) with | Sum.inl j => D.buying j | Sum.inr _ => p) = _
  rw [Equiv.symm_apply_apply]
@[simp] theorem leafPendantLength (D : BuyAtBulk.GraphData) (p : ℚ) (hp : 0 ≤ p)
    (j : Fin D.requestCount) (b : Bool) :
    (privateLeaves D p hp).length (leafPendantResource D p hp j b) = p := by
  change (match (Fintype.equivFin (Fin D.resourceCount ⊕ (Fin D.requestCount × Bool))).symm
    (Fintype.equivFin _ (Sum.inr (j,b))) with | Sum.inl j => D.length j | Sum.inr _ => p) = _
  rw [Equiv.symm_apply_apply]

/-- Exact length increase for every encoded path, including a nil original path. -/
theorem leafExtensionLength (D : BuyAtBulk.GraphData) (edge : EdgeOnlyInstance D)
    (p : ℚ) (hp : 0 ≤ p) (q : Fin D.toInstance.pathCount) :
    (privateLeaves D p hp).toInstance.pathLength (leafExtensionCode D p hp q) =
      D.toInstance.pathLength q + 2*p := by
  classical
  have hs (I : BuyAtBulk.Instance) (q : Fin I.pathCount) :
      I.pathLength q = ∑ a, if a ∈ I.uses q then I.length a else 0 := by
    simp [BuyAtBulk.Instance.pathLength]
  rw [hs, leafResourceSum]
  have old : (∑ a, if leafOldResource D p hp a ∈ (privateLeaves D p hp).toInstance.uses (leafExtensionCode D p hp q)
      then (privateLeaves D p hp).length (leafOldResource D p hp a) else 0) = D.toInstance.pathLength q := by
    rw [hs]
    apply Finset.sum_congr rfl
    intro a _
    have hm := leafExtensionCodeOldUses D edge p hp q a
    by_cases ha : a ∈ D.toInstance.uses q
    · simp only [if_pos ha, if_pos (hm.mpr ha)]; exact leafOldLength D p hp a
    · simp only [if_neg ha, if_neg (mt hm.mp ha)]
  change (∑ a, if leafOldResource D p hp a ∈ (privateLeaves D p hp).toInstance.uses _ then (privateLeaves D p hp).length _ else 0) + _ = _
  rw [old]
  congr 1
  have term (j : Fin D.requestCount) (b : Bool) :
      (if leafPendantResource D p hp j b ∈ (privateLeaves D p hp).toInstance.uses (leafExtensionCode D p hp q)
        then (privateLeaves D p hp).length (leafPendantResource D p hp j b) else 0) =
        if j = (D.decode q).1 then p else 0 := by
    have hm := leafExtensionCodePendantUses D p hp q j b
    by_cases h : j = (D.decode q).1
    · simp only [if_pos h, if_pos (hm.mpr h)]; exact leafPendantLength D p hp j b
    · simp only [if_neg h, if_neg (mt hm.mp h)]
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin D.requestCount))) rfl
    (fun j _ => Finset.sum_congr (s₁ := (Finset.univ : Finset Bool)) rfl (fun b _ => term j b))
  apply hsum.trans
  simp only [Fintype.sum_bool]
  rw [Finset.sum_add_distrib]
  simp [two_mul]
end BuyAtBulk.EdgeOnlyGap.ProofB
