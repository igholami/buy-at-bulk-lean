import BuyAtBulk.EdgeOnlyGap.Items.IntegralCostIdentity
import BuyAtBulk.EdgeOnlyGap.Items.RegularBase
import BuyAtBulk.EdgeOnlyGap.Items.Handshaking
import Mathlib.Tactic.Linarith

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 4: L>T branch, rental alone exceeds ng. -/
theorem longRoutingCost (H : FiniteGraph) (q d g : ℕ) (π : Lift H q)
    (hd : 0 < d) (base : RegularBase H d g)
    (r : (supplyData H q d π hd).toInstance.IntegralRouting)
    (large : threshold H g < totalCore H q d π hd r) :
  (H.n:ℚ)*g < (supplyData H q d π hd).toInstance.integralRentalCost r ∧
  2*(threshold H g:ℚ)/d = (H.n:ℚ)*g := by
  have hd_pos : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  have hhs : 2 * (requests H : ℚ) = (H.n : ℚ) * (d : ℚ) := by
    exact_mod_cast handshaking H d g base
  have hthresh : 2 * (threshold H g : ℚ) / d = (H.n : ℚ) * g := by
    unfold threshold
    push_cast
    rw [div_eq_iff (ne_of_gt hd_pos)]
    nlinarith [congrArg (fun x : ℚ => x * g) hhs]
  have hcost := (integralCostIdentity H q d π hd r).1
  unfold integralObjective at hcost
  have hbuy : (supplyData H q d π hd).toInstance.integralBuyingCost r =
      (spokeCount H q d π hd r : ℚ) := by
    classical
    unfold BuyAtBulk.Instance.integralBuyingCost spokeCount
    have h1 : ∀ a ∈ (supplyData H q d π hd).toInstance.usedResources r,
        (supplyData H q d π hd).toInstance.buying a =
        if ¬ coreResource H q d π hd a then 1 else 0 := by
      intro a _
      simp only [coreResource, supplyData, Sum.inr.injEq]
      split_ifs <;> simp_all
    rw [Finset.sum_congr rfl h1, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero,
      add_zero, nsmul_eq_mul, mul_one]
  have hrent : (supplyData H q d π hd).toInstance.integralRentalCost r =
      2 * (totalCore H q d π hd r : ℚ) / d := by linarith
  refine ⟨?_, hthresh⟩
  rw [hrent, ← hthresh]
  have hlt : (threshold H g : ℚ) < (totalCore H q d π hd r : ℚ) := by exact_mod_cast large
  exact div_lt_div_of_pos_right (by linarith) hd_pos

end BuyAtBulk.EdgeOnlyGap
