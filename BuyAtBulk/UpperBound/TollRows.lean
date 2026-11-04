import BuyAtBulk.UpperBound.NodeDistance
import BuyAtBulk.UpperBound.TollIncrement
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Fixed toll rows in the original node metric (Definition 4.2), before
purchases. Unreachable vertices receive zero toll. -/
namespace BuyAtBulk.Tolls

variable {V : Type} [Fintype V] (G : SimpleGraph V)

noncomputable def distanceTo (weight : V → ℚ) (s v : V) : ℚ := by
  classical
  exact if h : Nonempty (G.Path s v) then NodeMetric.distance G weight s v h else 0

noncomputable def row (buying physical : V → ℚ) (coefficient radius : ℚ) (s v : V) : ℚ := by
  classical
  exact if h : Nonempty (G.Path s v) then
    toll (buying v) radius (NodeMetric.distance G (fun a => buying a + coefficient * physical a) s v h)
  else 0

@[simp] theorem distanceTo_of_reachable (weight : V → ℚ) {s v : V}
    (h : Nonempty (G.Path s v)) :
    distanceTo G weight s v = NodeMetric.distance G weight s v h := by
  classical
  simp [distanceTo, h]

@[simp] theorem row_of_reachable (buying physical : V → ℚ) (coefficient radius : ℚ)
    {s v : V} (h : Nonempty (G.Path s v)) :
    row G buying physical coefficient radius s v =
      toll (buying v) radius (distanceTo G (fun a => buying a + coefficient * physical a) s v) := by
  classical
  simp [row, distanceTo, h]

theorem row_nonneg (buying physical : V → ℚ) (coefficient radius : ℚ) (s v : V) :
    0 ≤ row G buying physical coefficient radius s v := by
  classical
  unfold row
  split_ifs
  · exact toll_nonneg _ _ _
  · exact le_rfl

omit [Fintype V] in
theorem step_reachable {s u v : V} (hu : Nonempty (G.Path s u)) (edge : G.Adj u v) :
    Nonempty (G.Path s v) := by
  classical
  exact ⟨(hu.some.val.concat edge).toPath⟩

theorem row_increment (buying physical : V → ℚ) (coefficient radius : ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (coefficient_nonneg : 0 ≤ coefficient) {s u v : V}
    (hu : Nonempty (G.Path s u)) (edge : G.Adj u v) :
    min radius (distanceTo G (fun a => buying a + coefficient * physical a) s v) -
      min radius (distanceTo G (fun a => buying a + coefficient * physical a) s u) ≤
        row G buying physical coefficient radius s v + coefficient * physical v := by
  have hv := step_reachable G hu edge
  rw [row_of_reachable G buying physical coefficient radius hv]
  apply truncated_increment _ _ _ _ _ (buying_nonneg v)
    (mul_nonneg coefficient_nonneg (physical_nonneg v))
  simp only [distanceTo_of_reachable G _ hu, distanceTo_of_reachable G _ hv]
  have h := NodeMetric.distance_prefix G (fun a => buying a + coefficient * physical a)
    (fun a => add_nonneg (buying_nonneg a) (mul_nonneg coefficient_nonneg (physical_nonneg a))) hu hv edge
  simpa [add_assoc] using h

theorem row_bounds (buying physical : V → ℚ) (coefficient radius : ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (coefficient_nonneg : 0 ≤ coefficient) (radius_nonneg : 0 ≤ radius) (s v : V) :
    0 ≤ row G buying physical coefficient radius s v ∧
    row G buying physical coefficient radius s v ≤ min (buying v) radius := by
  classical
  refine ⟨row_nonneg G _ _ _ _ _ _, ?_⟩
  by_cases hv : Nonempty (G.Path s v)
  · rw [row_of_reachable G buying physical coefficient radius hv]
    apply le_min (toll_le_buying _ _ _ (buying_nonneg v))
    apply toll_le_radius _ _ _ radius_nonneg
    rw [distanceTo_of_reachable G _ hv]
    exact (le_add_of_nonneg_right (mul_nonneg coefficient_nonneg (physical_nonneg v))).trans
      (NodeMetric.endpoint_le_distance G _
        (fun a => add_nonneg (buying_nonneg a) (mul_nonneg coefficient_nonneg (physical_nonneg a))) hv)
  · simp [row, hv, le_min (buying_nonneg v) radius_nonneg]

end BuyAtBulk.Tolls
