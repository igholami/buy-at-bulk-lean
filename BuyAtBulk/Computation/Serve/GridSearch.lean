import BuyAtBulk.Computation.Attachment
import BuyAtBulk.UpperBound.GraphMainScale

/-! Executable finite-grid search. Indices increase as physical scales decrease,
so the minimum eligible index is the source's largest eligible scale. -/
namespace BuyAtBulk.Computation.Serve
open BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

def eligibleAt (buying physical : V → ℚ) (state : RoundingState G) (budget allowance : ℚ)
    (ratio : ℕ) (s t : V) (d : ℕ) : Bool :=
  decide ((gridScale budget ratio d : WithTop ℚ) ≤
    (ShortestPath.indexedDistances G (Attachment.mixedWeight G buying physical state allowance (gridScale budget ratio d))
      numbering t)[(numbering s).val])

def eligibleGrid (buying physical : V → ℚ) (state : RoundingState G) (budget allowance : ℚ)
    (h ratio : ℕ) (s t : V) : Finset ℕ :=
  (Finset.range (gridDepth h ratio + 1)).filter fun d => eligibleAt G numbering buying physical state budget allowance ratio s t d = true

def selectScale (buying physical : V → ℚ) (state : RoundingState G) (budget allowance : ℚ)
    (h ratio : ℕ) (s t : V) : Option ℕ :=
  let candidates := eligibleGrid G numbering buying physical state budget allowance h ratio s t
  if nonempty : candidates.Nonempty then some (candidates.min' nonempty) else none

theorem scale_nonneg (budget : ℚ) (budget_nonneg : 0 ≤ budget) (ratio depth : ℕ) :
    0 ≤ gridScale budget ratio depth := by
  unfold gridScale
  positivity

theorem eligibleAt_iff (buying physical : V → ℚ) (buying_nonneg : ∀ v, 0 ≤ buying v)
    (physical_nonneg : ∀ v, 0 ≤ physical v) (state : RoundingState G) (budget allowance : ℚ)
    (budget_nonneg : 0 ≤ budget) (allowance_pos : 0 < allowance) (ratio : ℕ) (s t : V)
    (reachable : Nonempty (G.Path s t)) (d : ℕ) :
    eligibleAt G numbering buying physical state budget allowance ratio s t d = true ↔
      gridScale budget ratio d ≤ NodeMetric.distance G
        (mixedNodeWeight G buying physical state allowance (gridScale budget ratio d)) s t reachable := by
  have correct := ShortestPath.indexedDistances_correct G
    (Attachment.mixedWeight G buying physical state allowance (gridScale budget ratio d))
    (Attachment.mixedWeight_nonneg G buying physical buying_nonneg physical_nonneg state allowance _ allowance_pos
      (scale_nonneg budget budget_nonneg ratio d)) numbering s t reachable
  unfold eligibleAt
  rw [correct]
  simp only [decide_eq_true_eq, WithTop.coe_le_coe, Attachment.mixedWeight_eq]

theorem eligibleGrid_eq (buying physical : V → ℚ) (buying_nonneg : ∀ v, 0 ≤ buying v)
    (physical_nonneg : ∀ v, 0 ≤ physical v) (state : RoundingState G) (budget allowance : ℚ)
    (budget_nonneg : 0 ≤ budget) (allowance_pos : 0 < allowance) (h ratio : ℕ) (s t : V)
    (reachable : Nonempty (G.Path s t)) :
    eligibleGrid G numbering buying physical state budget allowance h ratio s t =
      graphEligibleScales G buying physical state budget allowance h ratio s t reachable := by
  ext d
  simp only [eligibleGrid, graphEligibleScales, Finset.mem_filter]
  rw [eligibleAt_iff G numbering buying physical buying_nonneg physical_nonneg state budget allowance budget_nonneg allowance_pos ratio s t reachable d]

theorem selectScale_some (buying physical : V → ℚ) (buying_nonneg : ∀ v, 0 ≤ buying v)
    (physical_nonneg : ∀ v, 0 ≤ physical v) (state : RoundingState G) (budget allowance : ℚ)
    (budget_nonneg : 0 ≤ budget) (allowance_pos : 0 < allowance) (h ratio : ℕ) (s t : V)
    (reachable : Nonempty (G.Path s t)) (d : ℕ)
    (selected : selectScale G numbering buying physical state budget allowance h ratio s t = some d) :
    LargestEligibleScale G buying physical state budget allowance h ratio s t reachable d := by
  unfold selectScale at selected
  dsimp only at selected
  split at selected
  · rename_i nonempty
    have same := Option.some.inj selected
    subst d
    unfold LargestEligibleScale
    rw [← eligibleGrid_eq G numbering buying physical buying_nonneg physical_nonneg state budget allowance budget_nonneg allowance_pos h ratio s t reachable]
    exact ⟨Finset.min'_mem _ _, fun e member => Finset.min'_le _ e member⟩
  · contradiction

theorem selectScale_none (buying physical : V → ℚ) (buying_nonneg : ∀ v, 0 ≤ buying v)
    (physical_nonneg : ∀ v, 0 ≤ physical v) (state : RoundingState G) (budget allowance : ℚ)
    (budget_nonneg : 0 ≤ budget) (allowance_pos : 0 < allowance) (h ratio : ℕ) (s t : V)
    (reachable : Nonempty (G.Path s t))
    (selected : selectScale G numbering buying physical state budget allowance h ratio s t = none) :
    graphEligibleScales G buying physical state budget allowance h ratio s t reachable = ∅ := by
  unfold selectScale at selected
  dsimp only at selected
  split at selected
  · contradiction
  · rename_i empty
    rw [← eligibleGrid_eq G numbering buying physical buying_nonneg physical_nonneg state budget allowance budget_nonneg allowance_pos h ratio s t reachable]
    exact Finset.not_nonempty_iff_eq_empty.mp empty

/-- The executable attachment fuel reaches the cutoff at every selected grid
scale. This arithmetic lemma is independent of relational main totality. -/
theorem grid_deadline (budget : ℚ) (h ratio d : ℕ)
    (budget_nonneg : 0 ≤ budget) (h_pos : 0 < h) (ratio_ge : 2 ≤ ratio) :
    (gridScale budget ratio d / (ratio : ℚ)) / (ratio : ℚ) ^ gridDepth h ratio ≤ cutoff budget h ratio := by
  have hr : (1 : ℚ) ≤ ratio := by exact_mod_cast (show 1 ≤ ratio by omega)
  have hrpos : (0 : ℚ) < ratio := lt_of_lt_of_le (by norm_num) hr
  have power : (1 : ℚ) ≤ (ratio : ℚ) ^ d := one_le_pow₀ hr
  have scale_le : gridScale budget ratio d ≤ 2 * budget := by
    unfold gridScale
    apply (div_le_iff₀ (pow_pos hrpos d)).mpr
    nlinarith
  have lowered : gridScale budget ratio d / (ratio : ℚ) ≤ 2 * budget := by
    apply (div_le_iff₀ hrpos).mpr
    nlinarith
  exact (div_le_div_of_nonneg_right lowered (pow_nonneg hrpos.le (gridDepth h ratio))).trans
    (grid_smallest_le_cutoff budget h ratio budget_nonneg h_pos ratio_ge)

end BuyAtBulk.Computation.Serve
