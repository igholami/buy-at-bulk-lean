import BuyAtBulk.UpperBound.AuxiliaryBuying.Exchange
import BuyAtBulk.UpperBound.RunAuxTrace
import BuyAtBulk.UpperBound.GraphLPComparator

noncomputable section
namespace BuyAtBulk.UpperBound.NodeLP
open scoped BigOperators
variable {V : Type} [Fintype V] {G : SimpleGraph V} {h : ℕ}
local instance auxiliaryBuyingBoundDecEq : DecidableEq V := Classical.decEq V
local instance auxiliaryBuyingBoundDecRel : DecidableRel G.Adj := Classical.decRel _
variable (lp : NodeLP G h)

/-- Source `lem:buying`, for the actual sorted node-LP run. The proof extracts
both event logs, derives girth and paid-edge counts from physical guards,
exchanges the geometric sums once, and invokes the actual fixed-row packing
proof. No girth, packing, or cost-account certificate is assumed. -/
theorem run_buying_bound (allowance : Fin h → ℚ) (ratio r : ℕ)
    (budget_pos : 0 < lp.buyingBudget) (h_pos : 0 < h) (ratio_ge : 2 ≤ ratio) (r_ge : 1 ≤ r)
    (allowance_pos : ∀ i, 0 < allowance i)
    (length_bound : ∀ i, lp.fractionalLength i ≤ allowance i / 64)
    (selection : Helper.Selection (lp.fixedTollData allowance ratio budget_pos ratio_ge allowance_pos length_bound) h)
    {order : List (Fin h)} {before after : RoundingState G}
    (execution : RunExec G lp.buying lp.physical lp.buyingBudget ratio (6 * (r : ℚ) + 6)
      lp.source lp.target allowance order before after)
    (sorted : order.Pairwise fun i j => allowance i ≤ allowance j) (order_nodup : order.Nodup)
    (fresh_centers : before.centers = []) (fresh_edges : before.edges = [])
    (helper_bought : selection.nodes ⊆ before.bought)
    (zero_bought : ∀ v, lp.buying v = 0 → v ∈ before.bought) :
    (addedBuying G lp.buying before after : ℝ) ≤ (16 / 15 : ℝ) *
      ((lp.buyingBudget : ℝ) + ((ratio : ℝ) + 1 / 4) *
        (1 + (2 * (h : ℝ)) ^ (1 / (r : ℝ))) * ((ratio : ℝ) / ((ratio : ℝ) - 1)) *
        (1664 / 3) * (gridDepth h ratio) * lp.buyingBudget) := by
  have top : ∀ (state : RoundingState G) i (reachable : Nonempty (G.Path (lp.source i) (lp.target i))),
      NodeMetric.distance G (mixedNodeWeight G lp.buying lp.physical state (allowance i)
        (gridScale lp.buyingBudget ratio 0)) (lp.source i) (lp.target i) reachable <
          gridScale lp.buyingBudget ratio 0 := by
    intro state i reachable
    simpa only [gridScale, pow_zero, div_one] using
      lp.graph_top_scale_ineligible i state (allowance i) budget_pos (allowance_pos i) (length_bound i)
  have initialEligible : EdgesEligible G before := by
    intro edge member
    rw [fresh_edges] at member
    simp at member
  obtain ⟨auxEvents, auxTrace, auxMetadata, auxSorted, auxBounds, birthNonloops, account⟩ :=
    RunExec.auxiliary_trace lp.buying_nonneg lp.physical_nonneg budget_pos h_pos ratio_ge allowance_pos
      lp.source_buying lp.target_buying lp.source_physical lp.target_physical execution top initialEligible sorted
  obtain ⟨birthEvents, birthTrace, birthMetadata, birthBound⟩ :=
    lp.run_birth_scale_sum allowance ratio budget_pos h_pos ratio_ge allowance_pos length_bound selection
      (6 * (r : ℚ) + 6) execution sorted helper_bought
  have initialFree : ∀ record ∈ before.centers,
      lp.buying record.endpoint = 0 ∧ lp.physical record.endpoint = 0 := by
    intro record member
    rw [fresh_centers] at member
    simp at member
  have finalFree := run_final_centers_free lp.buying lp.physical lp.buyingBudget ratio
    lp.source lp.target allowance order birthTrace birthMetadata initialFree
    lp.source_buying lp.target_buying lp.source_physical lp.target_physical
  have centersBound := RunExec.centers_count_le_two_h G execution fresh_centers order_nodup
  have auxCovered : ∀ i : Fin auxEvents.length, ∃ d : Fin (gridDepth h ratio + 1),
      (auxEvents.get i).edge.scale = gridScale lp.buyingBudget ratio d := by
    intro i
    obtain ⟨_, _, _, _, d, hd, heq⟩ := auxMetadata (auxEvents.get i) (List.get_mem ..)
    exact ⟨⟨d, by omega⟩, heq⟩
  have birthCovered : ∀ i : Fin birthEvents.length, ∃ d : ℕ,
      (birthEvents.get i).scale = gridScale lp.buyingBudget ratio d := by
    intro i
    obtain ⟨_, _, _, _, d, hd, heq⟩ := birthMetadata (birthEvents.get i) (List.get_mem ..)
    exact ⟨d, heq⟩
  let A : ℝ := ((ratio : ℝ) + 1 / 4) * (1 + (2 * (h : ℝ)) ^ (1 / (r : ℝ))) *
    ((ratio : ℝ) / ((ratio : ℝ) - 1))
  have auxBound : (auxiliaryBuyingSum G lp.buying auxEvents : ℝ) ≤
      A * ∑ i : Fin birthEvents.length, ((birthEvents.get i).scale : ℝ) :=
    auxiliary_buying_le_birth_sum lp.physical_nonneg lp.buyingBudget budget_pos ratio ratio_ge r_ge
      (by linarith) auxTrace fresh_edges auxSorted auxBounds birthNonloops zero_bought finalFree
      centersBound auxCovered birthTrace fresh_centers birthCovered
  have birthBoundR : (∑ i : Fin birthEvents.length, ((birthEvents.get i).scale : ℝ)) ≤
      (1664 / 3 : ℝ) * (gridDepth h ratio) * lp.buyingBudget := by
    have hc : ((∑ i : Fin birthEvents.length, (birthEvents.get i).scale : ℚ) : ℝ) ≤
        (((1664 / 3 : ℚ) * (gridDepth h ratio) * lp.buyingBudget : ℚ) : ℝ) := by
      exact_mod_cast birthBound
    push_cast at hc
    exact hc
  have ratioReal : (2 : ℝ) ≤ ratio := by exact_mod_cast ratio_ge
  have ratioDenom : (0 : ℝ) < ratio - 1 := by linarith
  have A_nonneg : 0 ≤ A := by dsimp [A]; positivity
  have auxBudget : (auxiliaryBuyingSum G lp.buying auxEvents : ℝ) ≤
      A * (1664 / 3) * (gridDepth h ratio) * lp.buyingBudget := calc
    _ ≤ _ := auxBound
    _ ≤ A * ((1664 / 3) * (gridDepth h ratio) * lp.buyingBudget) :=
      mul_le_mul_of_nonneg_left birthBoundR A_nonneg
    _ = _ := by ring
  have requests_le : order.length ≤ h := by
    have card := Finset.card_le_univ order.toFinset
    rw [List.toFinset_card_of_nodup order_nodup] at card
    simpa using card
  have hq : (0 : ℚ) < h := by exact_mod_cast h_pos
  have baseCharge : (order.length : ℚ) * (lp.buyingBudget / h) ≤ lp.buyingBudget := by
    have hn : (order.length : ℚ) ≤ h := by exact_mod_cast requests_le
    have hm := mul_le_mul_of_nonneg_right hn (div_nonneg budget_pos.le hq.le)
    have cancel : (h : ℚ) * (lp.buyingBudget / h) = lp.buyingBudget := by
      field_simp [ne_of_gt hq]
    simpa only [cancel] using hm
  have baseChargeR : (order.length : ℝ) * ((lp.buyingBudget : ℝ) / h) ≤ lp.buyingBudget := by
    exact_mod_cast baseCharge
  have accountR : (addedBuying G lp.buying before after : ℝ) ≤ (16 / 15 : ℝ) *
      ((order.length : ℝ) * ((lp.buyingBudget : ℝ) / h) + auxiliaryBuyingSum G lp.buying auxEvents) := by
    have hc : (addedBuying G lp.buying before after : ℝ) ≤
        (((16 / 15 : ℚ) * ((order.length : ℚ) * (lp.buyingBudget / h) +
          auxiliaryBuyingSum G lp.buying auxEvents) : ℚ) : ℝ) := by
      exact_mod_cast account
    push_cast at hc
    exact hc
  calc
    _ ≤ _ := accountR
    _ ≤ (16 / 15 : ℝ) * ((lp.buyingBudget : ℝ) + A * (1664 / 3) *
        (gridDepth h ratio) * lp.buyingBudget) :=
      mul_le_mul_of_nonneg_left (add_le_add baseChargeR auxBudget) (by norm_num)
    _ = _ := by dsimp [A]

end BuyAtBulk.UpperBound.NodeLP
