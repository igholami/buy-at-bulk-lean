import BuyAtBulk.UpperBound.TollRows
import BuyAtBulk.UpperBound.PathCosts
import BuyAtBulk.UpperBound.AttachmentExecution

/-! Positive original tolls give short arms once the selected endpoint node is
bought. Their overlap would violate the actual later center-birth guard. -/
namespace BuyAtBulk.Tolls

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- Positive toll supplies an actual original shortest arm whose cost after
removing the endpoint's buying price is strictly below the row radius. -/
theorem positive_row_arm (buying physical : V → ℚ) (coefficient radius : ℚ) (s v : V)
    (positive : 0 < row G buying physical coefficient radius s v) :
    ∃ path : G.Path s v,
      NodeMetric.walkWeight G (fun a => buying a + coefficient * physical a) path.val - buying v < radius := by
  classical
  by_cases hv : Nonempty (G.Path s v)
  · rw [row_of_reachable G buying physical coefficient radius hv,
      distanceTo_of_reachable G _ hv] at positive
    obtain ⟨path, heq⟩ := NodeMetric.exists_shortest G
      (fun a => buying a + coefficient * physical a) hv
    refine ⟨path, ?_⟩
    unfold toll at positive
    have hmin := (lt_max_iff.mp positive).resolve_left (lt_irrefl 0)
    have hdist := hmin.trans_le (min_le_right _ _)
    rw [← heq] at hdist
    linarith
  · simp [row, hv] at positive

/-- A bought endpoint removes its buying contribution, while all physical
length remains. Increasing an allowance only decreases physical coefficients. -/
theorem bought_endpoint_arm_bound (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (state : UpperBound.RoundingState G) (scale oldAllowance newAllowance : ℚ)
    (scale_nonneg : 0 ≤ scale) (old_pos : 0 < oldAllowance) (new_pos : 0 < newAllowance)
    (order : oldAllowance ≤ newAllowance) {s v : V} (path : G.Path s v)
    (bought : v ∈ state.bought) :
    NodeMetric.walkWeight G (UpperBound.mixedNodeWeight G buying physical state newAllowance scale) path.val ≤
      NodeMetric.walkWeight G (fun a => buying a + (scale / oldAllowance) * physical a) path.val - buying v := by
  let current := UpperBound.mixedNodeWeight G buying physical state newAllowance scale
  change NodeMetric.walkWeight G current path.val ≤ _
  let : DecidableEq V := Classical.decEq V
  have coefficient : scale / newAllowance ≤ scale / oldAllowance := by
    apply (div_le_div_iff₀ new_pos old_pos).mpr
    nlinarith
  have per_node : ∀ a, current a ≤
      (buying a + (scale / oldAllowance) * physical a) - (if a = v then buying a else 0) := by
    intro a
    have hphysical := mul_le_mul_of_nonneg_right coefficient (physical_nonneg a)
    by_cases hav : a = v
    · subst a
      simp [current, UpperBound.mixedNodeWeight, bought]
      linarith
    · have hresidual : current a ≤ buying a + (scale / newAllowance) * physical a := by
        dsimp [current, UpperBound.mixedNodeWeight]
        split_ifs
        · have hb := buying_nonneg a
          linarith
        · exact le_rfl
      simp only [if_neg hav, sub_zero]
      linarith
  have hsum := Finset.sum_le_sum (s := path.val.support.toFinset) fun a _ => per_node a
  unfold NodeMetric.walkWeight
  rw [Finset.sum_sub_distrib] at hsum
  have endpoint_sum : (∑ a ∈ path.val.support.toFinset, if a = v then buying a else 0) = buying v := by
    rw [Finset.sum_eq_single v]
    · simp
    · intro a _ ha
      simp [ha]
    · intro hn
      exact False.elim (hn (List.mem_toFinset.mpr path.val.end_mem_support))
  rw [endpoint_sum] at hsum
  simpa only [NodeMetric.walkWeight] using hsum

/-- Two birth rows at one scale cannot share a positive toll on a bought node:
the later no-near-center branch would have an actual mixed-cost bypass. -/
theorem birth_rows_separated (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (state : UpperBound.RoundingState G) (scale oldAllowance newAllowance : ℚ)
    (scale_pos : 0 < scale) (old_pos : 0 < oldAllowance) (new_pos : 0 < newAllowance)
    (order : oldAllowance ≤ newAllowance) (oldCenter newEndpoint : V)
    (eligible : UpperBound.EligibleCenter state.centers oldCenter scale)
    (no_near : ¬ ∃ u, UpperBound.NearEligibleCenter G buying physical state newAllowance scale newEndpoint u)
    (v : V) (bought : v ∈ state.bought) :
    ¬ (0 < row G buying physical (scale / oldAllowance) (scale / 16) oldCenter v ∧
       0 < row G buying physical (scale / newAllowance) (scale / 16) newEndpoint v) := by
  classical
  rintro ⟨old_positive, new_positive⟩
  obtain ⟨oldPath, oldShort⟩ := positive_row_arm G buying physical _ _ _ _ old_positive
  obtain ⟨newPath, newShort⟩ := positive_row_arm G buying physical _ _ _ _ new_positive
  have old_bound := bought_endpoint_arm_bound G buying physical buying_nonneg physical_nonneg
    state scale oldAllowance newAllowance scale_pos.le old_pos new_pos order oldPath bought
  have new_bound := bought_endpoint_arm_bound G buying physical buying_nonneg physical_nonneg
    state scale newAllowance newAllowance scale_pos.le new_pos new_pos le_rfl newPath bought
  let route : G.Path newEndpoint oldCenter := (newPath.val.append oldPath.val.reverse).toPath
  have weight_nonneg := UpperBound.mixedWeight_nonneg G buying physical buying_nonneg physical_nonneg
    state newAllowance scale new_pos scale_pos.le
  have concatenated := UpperBound.walkWeight_append_le G
    (UpperBound.mixedNodeWeight G buying physical state newAllowance scale) weight_nonneg newPath.val oldPath.val.reverse
  have erased := NodeMetric.toPath_weight_le G
    (UpperBound.mixedNodeWeight G buying physical state newAllowance scale) weight_nonneg
    (newPath.val.append oldPath.val.reverse)
  have reverse_eq : NodeMetric.walkWeight G
      (UpperBound.mixedNodeWeight G buying physical state newAllowance scale) oldPath.val.reverse =
      NodeMetric.walkWeight G (UpperBound.mixedNodeWeight G buying physical state newAllowance scale) oldPath.val := by
    simp [NodeMetric.walkWeight, SimpleGraph.Walk.support_reverse]
  rw [reverse_eq] at concatenated
  apply no_near
  refine ⟨oldCenter, eligible, route, ?_⟩
  dsimp [route]
  linarith

/-- Actual mate-distance birth guard implies inclusion of the fixed original
row. Original reachability is supplied by the feasible LP, so the unreachable
zero convention cannot create a spurious included/excluded row. -/
theorem no_short_original_included (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (state : UpperBound.RoundingState G)
    (allowance scale radius : ℚ) (s t : V) (reachable : Nonempty (G.Path s t))
    (no_short : ¬ UpperBound.HasShortMixedRoute G buying physical state allowance scale s t radius) :
    radius < distanceTo G (fun a => buying a + (scale / allowance) * physical a) s t := by
  obtain ⟨path, shortest⟩ := NodeMetric.exists_shortest G
    (fun a => buying a + (scale / allowance) * physical a) reachable
  have comparator : NodeMetric.walkWeight G (UpperBound.mixedNodeWeight G buying physical state allowance scale) path.val ≤
      NodeMetric.walkWeight G (fun a => buying a + (scale / allowance) * physical a) path.val := by
    unfold NodeMetric.walkWeight
    apply Finset.sum_le_sum
    intro a _
    unfold UpperBound.mixedNodeWeight
    split_ifs
    · have hb := buying_nonneg a
      linarith
    · exact le_rfl
  by_contra hn
  have hle := not_lt.mp hn
  rw [distanceTo_of_reachable G _ reachable, ← shortest] at hle
  exact no_short ⟨path, comparator.trans hle⟩

end BuyAtBulk.Tolls
