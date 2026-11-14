import BuyAtBulk.Model.NodeReduction.Transport
import BuyAtBulk.EdgeOnlyGap.Items.LPObjective
import Mathlib.Tactic.Linarith
noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofB
open scoped BigOperators
open BuyAtBulk
attribute [local instance] Classical.propDecidable

/-- General finite-fiber restriction, allowing paths to merge and discarding resources. -/
theorem flowRestriction (I J : Instance)
    (req : Fin J.requestCount ≃ Fin I.requestCount)
    (res : Fin J.resourceCount → Fin I.resourceCount) (hinj : Function.Injective res)
    (map : Fin I.pathCount → Fin J.pathCount)
    (legal : ∀ i q, J.allowed i (map q) = I.allowed (req i) q)
    (uses : ∀ q a, a ∈ J.uses (map q) → res a ∈ I.uses q)
    (buy : ∀ a, J.buying a = I.buying (res a))
    (len : ∀ a, J.length a = I.length (res a))
    (dem : ∀ i, J.demand i = I.demand (req i))
    (f : I.FractionalSolution) (hf : I.Feasible f) :
    ∃ g : J.FractionalSolution, J.Feasible g ∧ lpObjective J g ≤ lpObjective I f := by
  classical
  let g : J.FractionalSolution := {
    opening := fun a => f.opening (res a)
    flow := fun i => NodeReduction.pushflow map (f.flow (req i)) }
  have hflow : ∀ i a, J.resourceFlow g i a ≤ I.resourceFlow f (req i) (res a) := by
    intro i a
    have hw := NodeReduction.weighted_pushflow map (f.flow (req i))
      (fun q => if a ∈ J.uses q then (1 : ℚ) else 0)
    change (∑ q, if a ∈ J.uses q then NodeReduction.pushflow map (f.flow (req i)) q else 0) ≤ _
    have he : (∑ q, if a ∈ J.uses q then NodeReduction.pushflow map (f.flow (req i)) q else 0) =
        ∑ q, (if a ∈ J.uses (map q) then (1 : ℚ) else 0) * f.flow (req i) q := by
      simpa only [ite_mul, one_mul, zero_mul] using hw
    rw [he]
    apply Finset.sum_le_sum
    intro q _
    by_cases ha : a ∈ J.uses (map q)
    · simp only [if_pos ha, one_mul, if_pos (uses q a ha)]
      exact le_rfl
    · simp only [if_neg ha, zero_mul]
      split_ifs <;> first | exact hf.2.1 (req i) q | exact le_rfl
  have hg : J.Feasible g := by
    refine ⟨fun a => hf.1 (res a), ?_, ?_, ?_, ?_⟩
    · intro i q
      change 0 ≤ ∑ t, if map t = q then f.flow (req i) t else 0
      exact Finset.sum_nonneg fun t _ => by split_ifs <;> first | exact hf.2.1 _ _ | exact le_rfl
    · intro i q hq
      change (∑ t, if map t = q then f.flow (req i) t else 0) = 0
      apply Finset.sum_eq_zero
      intro t _
      split_ifs with h
      · apply hf.2.2.1
        rw [← legal i t, h]
        exact hq
      · rfl
    · intro i
      have hw := NodeReduction.weighted_pushflow map (f.flow (req i)) (fun _ => (1 : ℚ))
      simpa only [one_mul, hf.2.2.2.1 (req i)] using hw
    · intro i a
      exact (hflow i a).trans (hf.2.2.2.2 (req i) (res a))
  have hb : J.buyingCost g ≤ I.buyingCost f := by
    unfold Instance.buyingCost
    apply Finset.sum_le_sum_of_injOn res
    · exact hinj.injOn
    · exact Finset.subset_univ _
    · intro a _; change J.buying a * f.opening (res a) ≤ _; rw [buy a]
    · intro a _ _; exact mul_nonneg (I.buying_nonneg a) (hf.1 a).1
  have hl : ∀ q, J.pathLength (map q) ≤ I.pathLength q := by
    intro q
    unfold Instance.pathLength
    apply Finset.sum_le_sum_of_injOn res
    · exact hinj.injOn
    · intro a ha
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
      exact uses q b hb
    · intro a _; exact le_of_eq (len a)
    · intro a _ _; exact I.length_nonneg a
  have hr : J.rentalCost g ≤ I.rentalCost f := by
    have per : ∀ i, J.fractionalLength g i ≤ I.fractionalLength f (req i) := by
      intro i
      have hw := NodeReduction.weighted_pushflow map (f.flow (req i)) J.pathLength
      change (∑ q, J.pathLength q * NodeReduction.pushflow map (f.flow (req i)) q) ≤ _
      rw [hw]
      exact Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_right (hl q) (hf.2.1 _ _)
    calc
      J.rentalCost g ≤ ∑ i, I.demand (req i) * I.fractionalLength f (req i) := by
        apply Finset.sum_le_sum
        intro i _
        rw [← dem i]
        exact mul_le_mul_of_nonneg_left (per i) (le_of_lt (J.demand_pos i))
      _ = I.rentalCost f := Equiv.sum_comp req (fun i => I.demand i * I.fractionalLength f i)
  exact ⟨g, hg, add_le_add hb hr⟩
end BuyAtBulk.EdgeOnlyGap.ProofB
