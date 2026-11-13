import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBFlowRestriction
noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofB
open scoped BigOperators
open BuyAtBulk
attribute [local instance] Classical.propDecidable

/-- Integral counterpart of resource-discarding finite-path restriction. -/
theorem integralRestriction (I J : Instance)
    (req : Fin J.requestCount ≃ Fin I.requestCount)
    (res : Fin J.resourceCount → Fin I.resourceCount) (hinj : Function.Injective res)
    (map : Fin I.pathCount → Fin J.pathCount)
    (legal : ∀ i q, J.allowed i (map q) = I.allowed (req i) q)
    (uses : ∀ q a, a ∈ J.uses (map q) → res a ∈ I.uses q)
    (buy : ∀ a, J.buying a = I.buying (res a))
    (len : ∀ a, J.length a = I.length (res a))
    (dem : ∀ i, J.demand i = I.demand (req i))
    (r : I.IntegralRouting) :
    ∃ s : J.IntegralRouting, integralObjective J s ≤ integralObjective I r := by
  classical
  let s : J.IntegralRouting := {
    path := fun i => map (r.path (req i))
    allowed_path := fun i => (legal i _).trans (r.allowed_path _) }
  have hu : ∀ a ∈ J.usedResources s, res a ∈ I.usedResources r := by
    intro a ha
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp ha
    exact Finset.mem_biUnion.mpr ⟨req i,Finset.mem_univ _,uses _ a hi⟩
  have hb : J.integralBuyingCost s ≤ I.integralBuyingCost r := by
    apply Finset.sum_le_sum_of_injOn res hinj.injOn
    · intro a ha
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
      exact hu b hb
    · intro a _; exact le_of_eq (buy a)
    · intro a _ _; exact I.buying_nonneg a
  have hl : ∀ q, J.pathLength (map q) ≤ I.pathLength q := by
    intro q
    apply Finset.sum_le_sum_of_injOn res hinj.injOn
    · intro a ha
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
      exact uses q b hb
    · intro a _; exact le_of_eq (len a)
    · intro a _ _; exact I.length_nonneg a
  have hr : J.integralRentalCost s ≤ I.integralRentalCost r := by
    calc
      J.integralRentalCost s ≤ ∑ i, I.demand (req i) * I.pathLength (r.path (req i)) := by
        apply Finset.sum_le_sum
        intro i _
        rw [← dem i]
        exact mul_le_mul_of_nonneg_left (hl _) (le_of_lt (J.demand_pos i))
      _ = I.integralRentalCost r := Equiv.sum_comp req (fun i => I.demand i * I.pathLength (r.path i))
  exact ⟨s,add_le_add hb hr⟩
end BuyAtBulk.EdgeOnlyGap.ProofB
