import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBLeafPrices
import BuyAtBulk.EdgeOnlyGap.Items.IntegralObjective
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.EdgeOnlyGap.ProofB
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- At zero pendant price, every integral routing extends with exactly the same cost. -/
theorem leafIntegralExtension (D : BuyAtBulk.GraphData) (edge : EdgeOnlyInstance D)
    (r : D.toInstance.IntegralRouting) :
    ∃ s : (privateLeaves D 0 (by norm_num)).toInstance.IntegralRouting,
      integralObjective (privateLeaves D 0 (by norm_num)).toInstance s = integralObjective D.toInstance r := by
  classical
  let hp : (0 : ℚ) ≤ 0 := le_rfl
  let s : (privateLeaves D 0 hp).toInstance.IntegralRouting := {
    path := fun i => leafExtensionCode D 0 hp (r.path i)
    allowed_path := fun i => (leafExtensionLegal D 0 hp i _).trans (r.allowed_path i) }
  have hu (a : Fin D.resourceCount) :
      leafOldResource D 0 hp a ∈ (privateLeaves D 0 hp).toInstance.usedResources s ↔ a ∈ D.toInstance.usedResources r := by
    simp only [BuyAtBulk.Instance.usedResources, Finset.mem_biUnion, Finset.mem_univ, true_and]
    apply exists_congr
    intro i
    exact leafExtensionCodeOldUses D edge 0 hp (r.path i) a
  have hb : (privateLeaves D 0 hp).toInstance.integralBuyingCost s = D.toInstance.integralBuyingCost r := by
    have hs (I : BuyAtBulk.Instance) (r : I.IntegralRouting) :
        I.integralBuyingCost r = ∑ a, if a ∈ I.usedResources r then I.buying a else 0 := by
      simp [BuyAtBulk.Instance.integralBuyingCost]
    rw [hs,leafResourceSum,hs]
    have ho : (∑ a, if leafOldResource D 0 hp a ∈ (privateLeaves D 0 hp).toInstance.usedResources s
        then (privateLeaves D 0 hp).buying (leafOldResource D 0 hp a) else 0) =
        ∑ a, if a ∈ D.toInstance.usedResources r then D.buying a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a ∈ D.toInstance.usedResources r
      · simp only [if_pos ha, if_pos ((hu a).mpr ha)]; exact leafOldBuying D 0 hp a
      · simp only [if_neg ha, if_neg (mt (hu a).mp ha)]
    change (∑ a, if leafOldResource D 0 hp a ∈ (privateLeaves D 0 hp).toInstance.usedResources s
      then (privateLeaves D 0 hp).buying (leafOldResource D 0 hp a) else 0) + _ = _
    rw [ho]
    have hz : (∑ j, ∑ b, if leafPendantResource D 0 hp j b ∈ (privateLeaves D 0 hp).toInstance.usedResources s
        then (privateLeaves D 0 hp).buying (leafPendantResource D 0 hp j b) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      apply Finset.sum_eq_zero
      intro b _
      split_ifs <;> first | exact leafPendantBuying D 0 hp j b | rfl
    rw [hz,add_zero]
  have hr : (privateLeaves D 0 hp).toInstance.integralRentalCost s = D.toInstance.integralRentalCost r := by
    apply Finset.sum_congr rfl
    intro i _
    change D.demand i * (privateLeaves D 0 hp).toInstance.pathLength (leafExtensionCode D 0 hp (r.path i)) = _
    rw [leafExtensionLength D edge 0 hp]
    simp only [mul_zero, add_zero]
  exact ⟨s, congrArg₂ (· + ·) hb hr⟩
end BuyAtBulk.EdgeOnlyGap.ProofB
