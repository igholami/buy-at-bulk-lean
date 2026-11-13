import BuyAtBulk.EdgeOnlyGap.Items.UsedCore
import BuyAtBulk.EdgeOnlyGap.Items.IntegralObjective
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import BuyAtBulk.EdgeOnlyGap.Items.PortRankNullity

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Equation (5), p. 3. -/
theorem integralCostIdentity (H : FiniteGraph) (q d : ℕ) (π : Lift H q) (hd : 0 < d)
    (r : (supplyData H q d π hd).toInstance.IntegralRouting) :
  integralObjective (supplyData H q d π hd).toInstance r =
    spokeCount H q d π hd r + 2 * (totalCore H q d π hd r : ℚ) / d ∧
  (usedCore H q d π hd r).card ≤ totalCore H q d π hd r := by
  classical
  let D := supplyData H q d π hd
  have hbuy : D.toInstance.integralBuyingCost r = (spokeCount H q d π hd r : ℚ) := by
    unfold BuyAtBulk.Instance.integralBuyingCost spokeCount
    have h1 : ∀ a ∈ D.toInstance.usedResources r,
        D.toInstance.buying a = if ¬ coreResource H q d π hd a then 1 else 0 := by
      intro a _
      simp only [D, coreResource, supplyData, Sum.inr.injEq]
      split_ifs <;> simp_all
    rw [Finset.sum_congr rfl h1, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero,
      add_zero, nsmul_eq_mul, mul_one]
  have hlen : ∀ i : Fin D.requestCount, D.toInstance.pathLength (r.path i) =
      2 * (coreTraversals H q d π hd r i : ℚ) / d := by
    intro i
    unfold BuyAtBulk.Instance.pathLength coreTraversals
    have h2 : ∀ a ∈ D.toInstance.uses (r.path i),
        D.toInstance.length a = if coreResource H q d π hd a then 2 / (d : ℚ) else 0 := by
      intro a _
      simp only [D, coreResource, supplyData, Sum.inr.injEq]
    rw [Finset.sum_congr rfl h2, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero,
      add_zero, nsmul_eq_mul]
    ring
  have hrent : D.toInstance.integralRentalCost r = 2 * (totalCore H q d π hd r : ℚ) / d := by
    unfold BuyAtBulk.Instance.integralRentalCost totalCore
    change (∑ i : Fin D.requestCount, 1 * D.toInstance.pathLength (r.path i)) = _
    trans ∑ i : Fin D.requestCount, 2 * (coreTraversals H q d π hd r i : ℚ) / d
    · exact Finset.sum_congr rfl (fun i _ => by simpa only [one_mul] using hlen i)
    push_cast
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    rfl
  refine ⟨by unfold integralObjective; rw [hbuy, hrent], ?_⟩
  let U := D.toInstance.usedResources r
  let C := U.filter (coreResource H q d π hd)
  have hprn := portRankNullity H q d π hd r
  have hdim : Module.finrank (ZMod 2) (portKernel H q d π hd r) +
      Module.finrank (ZMod 2) (LinearMap.range (portBoundary H q d π hd r)) = U.card := by
    have hrn := ProofB.rankNullity (portBoundary H q d π hd r)
    rw [Fintype.card_coe] at hrn
    exact hrn
  have hpart : spokeCount H q d π hd r + C.card = U.card := by
    rw [add_comm]
    exact Finset.card_filter_add_card_filter_not _
  have hcore_card : (usedCore H q d π hd r).card = C.card := by omega
  rw [hcore_card]
  have hC_biUnion : C = Finset.univ.biUnion fun i =>
      (D.toInstance.uses (r.path i)).filter (coreResource H q d π hd) := by
    ext a
    simp only [C, U, BuyAtBulk.Instance.usedResources, Finset.mem_filter,
      Finset.mem_biUnion, Finset.mem_univ, true_and]
    tauto
  rw [hC_biUnion]
  exact Finset.card_biUnion_le

end BuyAtBulk.EdgeOnlyGap
