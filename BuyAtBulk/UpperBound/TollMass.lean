import BuyAtBulk.UpperBound.TollRows
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! Fractional toll mass (Lemma 4.3). The toll increment is telescoped on actual
simple graph paths before averaging against the node LP's unit flow. -/
noncomputable section

namespace BuyAtBulk.Tolls

variable {V : Type} [Fintype V] (G : SimpleGraph V)

local instance tollMassLocalInst1 : DecidableEq V := Classical.decEq V
local instance tollMassLocalInst2 : DecidableRel G.Adj := Classical.decRel _

theorem walk_tail_bound (buying physical : V → ℚ) (coefficient radius : ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (coefficient_nonneg : 0 ≤ coefficient) (s : V) {u v : V} (walk : G.Walk u v) :
    Nonempty (G.Path s u) →
    min radius (distanceTo G (fun a => buying a + coefficient * physical a) s v) -
      min radius (distanceTo G (fun a => buying a + coefficient * physical a) s u) ≤
    (walk.support.tail.map fun a => row G buying physical coefficient radius s a +
      coefficient * physical a).sum := by
  induction walk with
  | nil => intro _; simp
  | @cons u w v edge tail ih =>
    intro hu
    have hw := step_reachable G hu edge
    have hs := row_increment G buying physical coefficient radius
      buying_nonneg physical_nonneg coefficient_nonneg hu edge
    have ht := ih hw
    have hsum : (tail.support.map fun a => row G buying physical coefficient radius s a +
        coefficient * physical a).sum =
      (row G buying physical coefficient radius s w + coefficient * physical w) +
        (tail.support.tail.map fun a => row G buying physical coefficient radius s a +
          coefficient * physical a).sum := by
      conv_lhs => rw [← tail.cons_tail_support]
      rfl
    simp only [SimpleGraph.Walk.support_cons, List.tail_cons]
    rw [hsum]
    linarith

theorem path_toll_bound (buying physical : V → ℚ) (coefficient radius : ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (coefficient_nonneg : 0 ≤ coefficient) (radius_nonneg : 0 ≤ radius)
    {s t : V} (source_buying : buying s = 0) (source_physical : physical s = 0)
    (path : G.Path s t)
    (included : radius ≤ distanceTo G (fun a => buying a + coefficient * physical a) s t) :
    radius ≤ NodeMetric.walkWeight G (row G buying physical coefficient radius s) path.val +
      coefficient * NodeMetric.walkWeight G physical path.val := by
  classical
  have h := walk_tail_bound G buying physical coefficient radius buying_nonneg physical_nonneg
    coefficient_nonneg s path.val ⟨SimpleGraph.Path.nil⟩
  have hd : distanceTo G (fun a => buying a + coefficient * physical a) s s = 0 := by
    rw [distanceTo_of_reachable G _ (show Nonempty (G.Path s s) from ⟨SimpleGraph.Path.nil⟩),
      NodeMetric.distance_self G _
        (fun a => add_nonneg (buying_nonneg a) (mul_nonneg coefficient_nonneg (physical_nonneg a)))]
    simp [source_buying, source_physical]
  rw [min_eq_left included, hd, min_eq_right radius_nonneg, sub_zero] at h
  have full : radius ≤ (path.val.support.map fun a =>
      row G buying physical coefficient radius s a + coefficient * physical a).sum := by
    conv_rhs => rw [← path.val.cons_tail_support]
    simp only [List.map_cons, List.sum_cons]
    exact h.trans (le_add_of_nonneg_left (add_nonneg
      (row_nonneg G _ _ _ _ _ _) (mul_nonneg coefficient_nonneg (physical_nonneg s))))
  rw [← List.sum_toFinset _ path.property.support_nodup] at full
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, NodeMetric.walkWeight] using full

theorem weighted_node_sum (nodeWeight : V → ℚ) {s t : V}
    (flow : G.Path s t → ℚ) :
    ∑ path, flow path * NodeMetric.walkWeight G nodeWeight path.val =
      ∑ v, nodeWeight v * ∑ path, if v ∈ path.val.support then flow path else 0 := by
  classical
  have expand : ∀ path : G.Path s t, NodeMetric.walkWeight G nodeWeight path.val =
      ∑ v, if v ∈ path.val.support then nodeWeight v else 0 := by
    intro path
    have hset : path.val.support.toFinset = Finset.univ.filter (fun v => v ∈ path.val.support) := by
      ext v
      simp
    unfold NodeMetric.walkWeight
    rw [hset, Finset.sum_filter]
  simp_rw [expand, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro path _
  split_ifs <;> ring

/-- The fractional mass lower bound, with the physical allowance already
expressed as its contribution to this radius. All flow assumptions are exactly
unit flow and the per-commodity natural node LP constraints. -/
theorem fractional_mass (buying physical opening : V → ℚ) (coefficient radius : ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (coefficient_nonneg : 0 ≤ coefficient) (radius_nonneg : 0 ≤ radius)
    {s t : V} (source_buying : buying s = 0) (source_physical : physical s = 0)
    (flow : G.Path s t → ℚ) (flow_nonneg : ∀ path, 0 ≤ flow path)
    (unit : ∑ path, flow path = 1)
    (capacity : ∀ v, (∑ path, if v ∈ path.val.support then flow path else 0) ≤ opening v)
    (included : radius ≤ distanceTo G (fun a => buying a + coefficient * physical a) s t)
    (physical_bound : coefficient * (∑ path, NodeMetric.walkWeight G physical path.val * flow path) ≤ radius / 4) :
    3 * radius / 4 ≤ ∑ v, opening v * row G buying physical coefficient radius s v := by
  classical
  have averaged := Finset.sum_le_sum (s := Finset.univ) fun path _ =>
    mul_le_mul_of_nonneg_left (path_toll_bound G buying physical coefficient radius
      buying_nonneg physical_nonneg coefficient_nonneg radius_nonneg
      source_buying source_physical path included) (flow_nonneg path)
  have hleft : (∑ path, flow path * radius) = radius := by
    rw [← Finset.sum_mul, unit, one_mul]
  rw [hleft] at averaged
  have hright : (∑ path, flow path * (NodeMetric.walkWeight G
      (row G buying physical coefficient radius s) path.val +
        coefficient * NodeMetric.walkWeight G physical path.val)) =
      (∑ path, flow path * NodeMetric.walkWeight G
        (row G buying physical coefficient radius s) path.val) +
      coefficient * (∑ path, NodeMetric.walkWeight G physical path.val * flow path) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro path _
    ring
  rw [hright, weighted_node_sum] at averaged
  have toll_bound : (∑ v, row G buying physical coefficient radius s v *
      ∑ path, if v ∈ path.val.support then flow path else 0) ≤
      ∑ v, opening v * row G buying physical coefficient radius s v := by
    apply Finset.sum_le_sum
    intro v _
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (capacity v)
      (row_nonneg G buying physical coefficient radius s v)
  linarith

/-- Lemma 4.3 in the paper's original scale and physical-allowance notation. -/
theorem fractional_toll_mass (buying physical opening : V → ℚ) (scale allowance : ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (scale_pos : 0 < scale) (allowance_pos : 0 < allowance)
    {s t : V} (source_buying : buying s = 0) (source_physical : physical s = 0)
    (flow : G.Path s t → ℚ) (flow_nonneg : ∀ path, 0 ≤ flow path)
    (unit : ∑ path, flow path = 1)
    (capacity : ∀ v, (∑ path, if v ∈ path.val.support then flow path else 0) ≤ opening v)
    (included : scale / 16 < distanceTo G (fun a => buying a + (scale / allowance) * physical a) s t)
    (allowance_bound : (∑ path, NodeMetric.walkWeight G physical path.val * flow path) ≤ allowance / 64) :
    3 * (scale / 16) / 4 ≤
      ∑ v, opening v * row G buying physical (scale / allowance) (scale / 16) s v := by
  apply fractional_mass G buying physical opening (scale / allowance) (scale / 16)
    buying_nonneg physical_nonneg (div_nonneg scale_pos.le allowance_pos.le)
    (by positivity) source_buying source_physical flow flow_nonneg unit capacity included.le
  calc
    _ ≤ (scale / allowance) * (allowance / 64) :=
      mul_le_mul_of_nonneg_left allowance_bound (div_nonneg scale_pos.le allowance_pos.le)
    _ = _ := by field_simp; ring

end BuyAtBulk.Tolls
