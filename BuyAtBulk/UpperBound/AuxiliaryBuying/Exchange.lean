import BuyAtBulk.UpperBound.AuxiliaryBuying.Costs

noncomputable section
namespace BuyAtBulk.UpperBound
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Actual edge charges exchange into actual birth scales exactly once. The
proof uses trace-derived girth/simplicity and the finite geometric tail sum;
no packing or buying-account conclusion is an input. -/
theorem auxiliary_buying_le_birth_sum {buying physical : V → ℚ}
    (physical_nonneg : ∀ v, 0 ≤ physical v) (budget : ℚ) (budget_pos : 0 < budget)
    (ratio : ℕ) (ratio_ge : 2 ≤ ratio) {Q : ℚ} {r h lastDepth : ℕ}
    (hr : 1 ≤ r) (hQ : 6 * (r : ℚ) ≤ Q)
    {before after : RoundingState G} {auxEvents : List (AuxiliaryEvent G)}
    (auxTrace : AuxiliaryTrace G physical Q before auxEvents after) (freshEdges : before.edges = [])
    (sorted : auxEvents.Pairwise fun earlier later => earlier.allowance ≤ later.allowance)
    (bounds : ∀ event ∈ auxEvents, AuxiliaryBounds G buying physical ratio event)
    (nonloopBirths : BirthEdgesNonloop G auxEvents)
    (zero_bought : ∀ v, buying v = 0 → v ∈ before.bought)
    (centers_free : ∀ record ∈ after.centers, buying record.endpoint = 0 ∧ physical record.endpoint = 0)
    (centers_bound : after.centers.length ≤ 2 * h)
    (auxCovered : ∀ i : Fin auxEvents.length, ∃ d : Fin (lastDepth + 1),
      (auxEvents.get i).edge.scale = gridScale budget ratio d)
    {birthEvents : List (BirthEvent G)} (birthTrace : BirthTrace G buying physical before birthEvents after)
    (freshCenters : before.centers = [])
    (birthCovered : ∀ i : Fin birthEvents.length, ∃ d : ℕ,
      (birthEvents.get i).scale = gridScale budget ratio d) :
    (auxiliaryBuyingSum G buying auxEvents : ℝ) ≤
      ((ratio : ℝ) + 1 / 4) * (1 + (2 * (h : ℝ)) ^ (1 / (r : ℝ))) *
        ((ratio : ℝ) / ((ratio : ℝ) - 1)) * ∑ i : Fin birthEvents.length, ((birthEvents.get i).scale : ℝ) := by
  let U : ℝ := 1 + (2 * (h : ℝ)) ^ (1 / (r : ℝ))
  have U_nonneg : 0 ≤ U := by dsimp [U]; positivity
  have counts := AuxiliaryGraph.trace_paid_bound_of_free physical_nonneg hr hQ auxTrace freshEdges
    sorted bounds nonloopBirths zero_bought centers_free centers_bound
  have scalesQ := auxiliary_scales_le_counts auxTrace freshEdges budget budget_pos.le ratio lastDepth auxCovered
  have scalesR : (∑ i : Fin auxEvents.length, ((auxEvents.get i).edge.scale : ℝ)) ≤
      ∑ d : Fin (lastDepth + 1), (gridScale budget ratio d : ℝ) *
        ((after.edges.filter fun edge => edge.scale = gridScale budget ratio d).length : ℝ) := by
    exact_mod_cast scalesQ
  have cumulativeQ := cumulative_record_scale_sum birthTrace freshCenters budget budget_pos ratio ratio_ge lastDepth birthCovered
  have cumulativeR : (∑ d : Fin (lastDepth + 1), (gridScale budget ratio d : ℝ) *
      ((after.centers.filter fun record => gridScale budget ratio d ≤ record.birthScale).length : ℝ)) ≤
      ((ratio : ℝ) / ((ratio : ℝ) - 1)) * ∑ i : Fin birthEvents.length, ((birthEvents.get i).scale : ℝ) := by
    exact_mod_cast cumulativeQ
  have scaleSum : (∑ i : Fin auxEvents.length, ((auxEvents.get i).edge.scale : ℝ)) ≤
      U * (((ratio : ℝ) / ((ratio : ℝ) - 1)) * ∑ i : Fin birthEvents.length, ((birthEvents.get i).scale : ℝ)) := calc
    _ ≤ _ := scalesR
    _ ≤ ∑ d : Fin (lastDepth + 1), (gridScale budget ratio d : ℝ) *
        (U * ((after.centers.filter fun record => gridScale budget ratio d ≤ record.birthScale).length : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left (counts (gridScale budget ratio d))
      unfold gridScale
      positivity
    _ = U * ∑ d : Fin (lastDepth + 1), (gridScale budget ratio d : ℝ) *
        ((after.centers.filter fun record => gridScale budget ratio d ≤ record.birthScale).length : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left cumulativeR U_nonneg
  have costsQ := auxiliary_cost_le_scale_sum buying physical ratio auxEvents bounds
  have costsR : (auxiliaryBuyingSum G buying auxEvents : ℝ) ≤ ((ratio : ℝ) + 1 / 4) *
      ∑ i : Fin auxEvents.length, ((auxEvents.get i).edge.scale : ℝ) := by
    have hc : (auxiliaryBuyingSum G buying auxEvents : ℝ) ≤
        (((ratio : ℚ) + 1 / 4) * (∑ i : Fin auxEvents.length, (auxEvents.get i).edge.scale) : ℚ) := by
      exact_mod_cast costsQ
    push_cast at hc
    exact hc
  calc
    _ ≤ _ := costsR
    _ ≤ ((ratio : ℝ) + 1 / 4) *
        (U * (((ratio : ℝ) / ((ratio : ℝ) - 1)) * ∑ i : Fin birthEvents.length, ((birthEvents.get i).scale : ℝ))) :=
      mul_le_mul_of_nonneg_left scaleSum (by positivity)
    _ = _ := by dsimp [U]; ring

end BuyAtBulk.UpperBound
