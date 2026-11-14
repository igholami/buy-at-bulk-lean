import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBLeafPrices
import BuyAtBulk.EdgeOnlyGap.Items.LPObjective
import Mathlib.Tactic.Ring
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.EdgeOnlyGap.ProofB
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def leafExtendedFractional (D : BuyAtBulk.GraphData) (p : ℚ) (hp : 0 ≤ p)
    (f : D.toInstance.FractionalSolution) : (privateLeaves D p hp).toInstance.FractionalSolution where
  opening a := match (Fintype.equivFin (Fin D.resourceCount ⊕ (Fin D.requestCount × Bool))).symm a with
    | Sum.inl j => f.opening j | Sum.inr _ => 1
  flow i := BuyAtBulk.NodeReduction.pushflow (leafExtensionCode D p hp) (f.flow i)

@[simp] theorem leafExtendedOpeningOld (D : BuyAtBulk.GraphData) (p : ℚ) (hp : 0 ≤ p)
    (f : D.toInstance.FractionalSolution) (a : Fin D.resourceCount) :
    (leafExtendedFractional D p hp f).opening (leafOldResource D p hp a) = f.opening a := by
  change (match (Fintype.equivFin (Fin D.resourceCount ⊕ (Fin D.requestCount × Bool))).symm
    (Fintype.equivFin _ (Sum.inl a)) with | Sum.inl j => f.opening j | Sum.inr _ => 1) = _
  rw [Equiv.symm_apply_apply]
@[simp] theorem leafExtendedOpeningPendant (D : BuyAtBulk.GraphData) (p : ℚ) (hp : 0 ≤ p)
    (f : D.toInstance.FractionalSolution) (j : Fin D.requestCount) (b : Bool) :
    (leafExtendedFractional D p hp f).opening (leafPendantResource D p hp j b) = 1 := by
  change (match (Fintype.equivFin (Fin D.resourceCount ⊕ (Fin D.requestCount × Bool))).symm
    (Fintype.equivFin _ (Sum.inr (j,b))) with | Sum.inl j => f.opening j | Sum.inr _ => 1) = _
  rw [Equiv.symm_apply_apply]

theorem leafExtendedFeasible (D : BuyAtBulk.GraphData) (edge : EdgeOnlyInstance D)
    (p : ℚ) (hp : 0 ≤ p) (f : D.toInstance.FractionalSolution) (hf : D.toInstance.Feasible f) :
    (privateLeaves D p hp).toInstance.Feasible (leafExtendedFractional D p hp f) := by
  classical
  have resource_cases : ∀ a : Fin (privateLeaves D p hp).resourceCount,
      (∃ b, a = leafOldResource D p hp b) ∨
      (∃ j b, a = leafPendantResource D p hp j b) := by
    intro a
    obtain ⟨r,rfl⟩ := (Fintype.equivFin (Fin D.resourceCount ⊕ (Fin D.requestCount × Bool))).surjective a
    rcases r with b | ⟨j,b⟩
    · exact Or.inl ⟨b,rfl⟩
    · exact Or.inr ⟨j,b,rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a
    rcases resource_cases a with ⟨b,rfl⟩ | ⟨j,b,rfl⟩
    · exact (leafExtendedOpeningOld D p hp f b).symm ▸ hf.1 b
    · rw [leafExtendedOpeningPendant]; exact ⟨zero_le_one,le_rfl⟩
  · intro i q
    change 0 ≤ ∑ t, if leafExtensionCode D p hp t = q then f.flow i t else 0
    exact Finset.sum_nonneg fun t _ => by split_ifs <;> first | exact hf.2.1 _ _ | exact le_rfl
  · intro i q hq
    change (∑ t, if leafExtensionCode D p hp t = q then f.flow i t else 0) = 0
    apply Finset.sum_eq_zero
    intro t _
    split_ifs with h
    · apply hf.2.2.1
      rw [← leafExtensionLegal D p hp i t, h]
      exact hq
    · rfl
  · intro i
    have hw := BuyAtBulk.NodeReduction.weighted_pushflow (leafExtensionCode D p hp) (f.flow i) (fun _ => (1 : ℚ))
    simpa only [one_mul, hf.2.2.2.1 i, leafExtendedFractional] using hw
  · intro i a
    have hw := BuyAtBulk.NodeReduction.weighted_pushflow (leafExtensionCode D p hp) (f.flow i)
      (fun q => if a ∈ (privateLeaves D p hp).toInstance.uses q then (1 : ℚ) else 0)
    have he : (privateLeaves D p hp).toInstance.resourceFlow (leafExtendedFractional D p hp f) i a =
        ∑ t, if a ∈ (privateLeaves D p hp).toInstance.uses (leafExtensionCode D p hp t) then f.flow i t else 0 := by
      simpa only [BuyAtBulk.Instance.resourceFlow, leafExtendedFractional, ite_mul, one_mul, zero_mul] using hw
    rw [he]
    rcases resource_cases a with ⟨b,rfl⟩ | ⟨j,b,rfl⟩
    · simp only [leafExtensionCodeOldUses D edge p hp, leafExtendedOpeningOld]
      exact hf.2.2.2.2 i b
    · rw [show (leafExtendedFractional D p hp f).opening (leafPendantResource D p hp j b) = 1 from leafExtendedOpeningPendant D p hp f j b]
      rw [← hf.2.2.2.1 i]
      exact Finset.sum_le_sum fun t _ => by split_ifs <;> first | exact le_rfl | exact hf.2.1 _ _

/-- Extension of every feasible fractional solution has exactly two opening and two rental pendants per request. -/
theorem leafExtendedCost (D : BuyAtBulk.GraphData) (edge : EdgeOnlyInstance D)
    (p : ℚ) (hp : 0 ≤ p) (f : D.toInstance.FractionalSolution) (hf : D.toInstance.Feasible f) :
    lpObjective (privateLeaves D p hp).toInstance (leafExtendedFractional D p hp f) =
      lpObjective D.toInstance f + 4*D.requestCount*p := by
  classical
  have hb : (privateLeaves D p hp).toInstance.buyingCost (leafExtendedFractional D p hp f) = D.toInstance.buyingCost f + 2*D.requestCount*p := by
    unfold BuyAtBulk.Instance.buyingCost
    rw [leafResourceSum]
    simp only [leafOldBuying, leafPendantBuying, leafExtendedOpeningOld, leafExtendedOpeningPendant,
      mul_one, Fintype.sum_bool, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_bool, Nat.cast_ofNat, nsmul_eq_mul]
    ring
  have hl : ∀ i : Fin D.requestCount, (privateLeaves D p hp).toInstance.fractionalLength (leafExtendedFractional D p hp f) i = D.toInstance.fractionalLength f i + 2*p := by
    intro i
    have hw := BuyAtBulk.NodeReduction.weighted_pushflow (leafExtensionCode D p hp) (f.flow i) (privateLeaves D p hp).toInstance.pathLength
    change (∑ q, (privateLeaves D p hp).toInstance.pathLength q * BuyAtBulk.NodeReduction.pushflow (leafExtensionCode D p hp) (f.flow i) q) = _
    rw [hw]
    simp_rw [leafExtensionLength D edge p hp, add_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hf.2.2.2.1 i, mul_one]
    rfl
  have hr : (privateLeaves D p hp).toInstance.rentalCost (leafExtendedFractional D p hp f) = D.toInstance.rentalCost f + 2*D.requestCount*p := by
    change (∑ i, D.demand i * (privateLeaves D p hp).toInstance.fractionalLength (leafExtendedFractional D p hp f) i) = _
    simp_rw [hl, edge.1, one_mul]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_bool, Nat.cast_ofNat, nsmul_eq_mul]
    have hd : D.toInstance.rentalCost f = ∑ i, D.toInstance.fractionalLength f i := by
      change (∑ i, D.demand i * D.toInstance.fractionalLength f i) = _
      simp only [edge.1, one_mul]
    rw [hd]
    ring
  unfold lpObjective
  rw [hb,hr]
  ring
end BuyAtBulk.EdgeOnlyGap.ProofB
