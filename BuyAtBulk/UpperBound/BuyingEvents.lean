import BuyAtBulk.UpperBound.BuyingCosts
import BuyAtBulk.UpperBound.InheritedArm

/-! The buying and physical-realization estimates for the actual terminal
birth/purchase branches in `lem:attachment`. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

theorem two_path_buying_le (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (state : RoundingState G) (allowance scale : ℚ) (allowance_pos : 0 < allowance) (scale_nonneg : 0 ≤ scale)
    {a b c d : V} (first : G.Path a b) (second : G.Path c d) :
    addedBuying G buying state (buyPath G (buyPath G state first) second) ≤
      NodeMetric.walkWeight G (mixedNodeWeight G buying physical state allowance scale) first.val +
      NodeMetric.walkWeight G (mixedNodeWeight G buying physical state allowance scale) second.val := by
  have first_le := buyPath_addedBuying_le_mixed G buying physical physical_nonneg state allowance scale allowance_pos scale_nonneg first
  have second_le := buyPath_addedBuying_le_mixed G buying physical physical_nonneg (buyPath G state first)
    allowance scale allowance_pos scale_nonneg second
  have mixed_le := mixed_walk_bought_mono G buying physical buying_nonneg state (buyPath G state first)
    (bought_subset_buyPath G state first) allowance scale second
  rw [addedBuying_trans G buying state (buyPath G state first)]
  linarith

theorem attachment_birth_buying (buying physical : V → ℚ)
    (physical_nonneg : ∀ v, 0 ≤ physical v) (state : RoundingState G)
    (allowance ratio scale : ℚ) (allowance_pos : 0 < allowance) (ratio_ge : 1 ≤ ratio) (scale_nonneg : 0 ≤ scale)
    {z u : V} (path : G.Path z u)
    (inherited : NodeMetric.walkWeight G (mixedNodeWeight G buying physical state allowance scale) path.val ≤ (ratio / 8) * scale) :
    addedBuying G buying state (recordEdge G (buyPath G (recordBirth G state z scale) path) path scale) ≤
      (ratio + 1 / 4) * scale := by
  have buying_le := (buyPath_addedBuying_le_mixed G buying physical physical_nonneg state allowance scale allowance_pos scale_nonneg path).trans inherited
  have same_cost : addedBuying G buying state (recordEdge G (buyPath G (recordBirth G state z scale) path) path scale) =
      addedBuying G buying state (buyPath G state path) := by rfl
  rw [same_cost]
  nlinarith

theorem attachment_purchase_buying (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (state : RoundingState G) (allowance ratio scale : ℚ)
    (allowance_pos : 0 < allowance) (ratio_ge : 1 ≤ ratio) (scale_nonneg : 0 ≤ scale)
    {z u v : V} (inherited : G.Path z u) (near : G.Path z v)
    (inherited_bound : NodeMetric.walkWeight G (mixedNodeWeight G buying physical state allowance scale)
      inherited.val ≤ (ratio / 8) * scale)
    (near_bound : NodeMetric.walkWeight G (mixedNodeWeight G buying physical state allowance scale)
      near.val ≤ scale / 8) :
    addedBuying G buying state (recordEdge G (buyPath G (buyPath G state inherited) near)
      (inherited.val.reverse.append near.val).toPath scale) ≤ (ratio + 1 / 4) * scale := by
  have buying_le := two_path_buying_le G buying physical buying_nonneg physical_nonneg state allowance scale
    allowance_pos scale_nonneg inherited near
  change addedBuying G buying state (buyPath G (buyPath G state inherited) near) ≤ _
  nlinarith

theorem attachment_purchase_realization (physical : V → ℚ) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (allowance : ℚ) (allowance_pos : 0 < allowance) {z u v : V}
    (inherited : G.Path z u) (near : G.Path z v)
    (inherited_bound : NodeMetric.walkWeight G physical inherited.val ≤ allowance / 8)
    (near_bound : NodeMetric.walkWeight G physical near.val ≤ allowance / 8) :
    NodeMetric.walkWeight G physical (inherited.val.reverse.append near.val).toPath.val < 3 * allowance := by
  have concat_bound := walkWeight_append_le G physical physical_nonneg inherited.val.reverse near.val
  have erased := NodeMetric.toPath_weight_le G physical physical_nonneg (inherited.val.reverse.append near.val)
  have reverse_eq : NodeMetric.walkWeight G physical inherited.val.reverse = NodeMetric.walkWeight G physical inherited.val := by
    simp [NodeMetric.walkWeight, SimpleGraph.Walk.support_reverse]
  rw [reverse_eq] at concat_bound
  linarith

end BuyAtBulk.UpperBound
