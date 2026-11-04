import BuyAtBulk.UpperBound.MainArms
import BuyAtBulk.UpperBound.MainChoice
import BuyAtBulk.UpperBound.BuyingCosts

/-! Actual main-purchase buying and auxiliary physical realization estimates
in `lem:main-paths`, with both arm assignments performed before buying. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

theorem mainChoice_residual_buying (buying physical : V → ℚ) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (state : RoundingState G) (budget allowance : ℚ) (h ratio : ℕ) (s t : V)
    (reachable : Nonempty (G.Path s t)) (budget_pos : 0 < budget) (allowance_pos : 0 < allowance) (ratio_pos : 0 < ratio)
    (top_ineligible : NodeMetric.distance G (mixedNodeWeight G buying physical state allowance (gridScale budget ratio 0)) s t reachable < gridScale budget ratio 0)
    (choice : MainChoice G buying physical state budget allowance h ratio s t reachable) :
    residualWalkBuying G buying state choice.mainPath ≤ (ratio : ℚ) * gridScale budget ratio choice.index := by
  have ineligible := (largest_scale_predecessor_ineligible G buying physical state budget allowance h ratio s t reachable
    top_ineligible choice.index choice.largest).2.2
  have heq := shortest_weight_eq_distance G _ reachable choice.mainPath choice.shortest
  have hr : (ratio : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ratio_pos)
  have scale_pos : 0 < gridScale budget ratio (choice.index-1) := by unfold gridScale; positivity
  have cost := (residualBuying_le_mixed G buying physical physical_nonneg state allowance _ allowance_pos scale_pos.le choice.mainPath).trans (heq.trans_lt ineligible).le
  have hd : choice.index = (choice.index-1)+1 := by have := choice.positive; omega
  have previous_eq : gridScale budget ratio (choice.index-1) = (ratio : ℚ) * gridScale budget ratio choice.index := by
    conv_rhs => rw [gridScale, hd, pow_succ]
    unfold gridScale
    field_simp
  simpa only [previous_eq] using cost

theorem main_purchase_buying {buying physical : V → ℚ} {budget allowance : ℚ} {h ratio : ℕ}
    {s t u v : V} {reachable : Nonempty (G.Path s t)} {before first assigned : RoundingState G}
    {bornS bornT : Bool} {sarm : G.Path s u} {tarm : G.Path t v}
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (budget_pos : 0 < budget) (allowance_pos : 0 < allowance) (ratio_pos : 0 < ratio)
    (terminal_buying : buying s = 0 ∧ buying t = 0) (terminal_physical : physical s = 0 ∧ physical t = 0)
    (top_ineligible : NodeMetric.distance G (mixedNodeWeight G buying physical before allowance (gridScale budget ratio 0)) s t reachable < gridScale budget ratio 0)
    (choice : MainChoice G buying physical before budget allowance h ratio s t reachable)
    (assignS : CenterAssignment G buying physical allowance (gridScale budget ratio choice.index) s before first bornS u sarm)
    (assignT : CenterAssignment G buying physical allowance (gridScale budget ratio choice.index) t first assigned bornT v tarm) :
    addedBuying G buying assigned (buyPath G (buyPath G (buyPath G assigned sarm) choice.mainPath) tarm) ≤
      ((ratio : ℚ) + 1 / 4) * gridScale budget ratio choice.index := by
  have hr : 0 < (ratio : ℚ) := by exact_mod_cast ratio_pos
  have scale_pos : 0 < gridScale budget ratio choice.index := by unfold gridScale; positivity
  have boughtS : before.bought ⊆ assigned.bought := by rw [assignT.bought_eq, assignS.bought_eq]
  have boughtT : first.bought ⊆ assigned.bought := by rw [assignT.bought_eq]
  have s_le := (residualWalkBuying_mono G buying buying_nonneg before assigned boughtS sarm).trans
    ((residualBuying_le_mixed G buying physical physical_nonneg before allowance _ allowance_pos scale_pos.le sarm).trans
      (CenterAssignment.arm_short G assignS terminal_buying.1 terminal_physical.1 scale_pos.le))
  have t_le := (residualWalkBuying_mono G buying buying_nonneg first assigned boughtT tarm).trans
    ((residualBuying_le_mixed G buying physical physical_nonneg first allowance _ allowance_pos scale_pos.le tarm).trans
      (CenterAssignment.arm_short G assignT terminal_buying.2 terminal_physical.2 scale_pos.le))
  have main_le := (residualWalkBuying_mono G buying buying_nonneg before assigned boughtS choice.mainPath).trans
    (mainChoice_residual_buying G buying physical physical_nonneg before budget allowance h ratio s t reachable
      budget_pos allowance_pos ratio_pos top_ineligible choice)
  have all_paths := three_path_buying_le G buying buying_nonneg assigned sarm choice.mainPath tarm
  linarith

theorem main_purchase_realization (physical : V → ℚ) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (allowance : ℚ) (allowance_pos : 0 < allowance) {s t u v : V}
    (sarm : G.Path s u) (main : G.Path s t) (tarm : G.Path t v)
    (s_bound : NodeMetric.walkWeight G physical sarm.val ≤ allowance / 8)
    (main_bound : NodeMetric.walkWeight G physical main.val ≤ allowance)
    (t_bound : NodeMetric.walkWeight G physical tarm.val ≤ allowance / 8) :
    NodeMetric.walkWeight G physical ((sarm.val.reverse.append main.val).append tarm.val).toPath.val < 3 * allowance := by
  have inner := walkWeight_append_le G physical physical_nonneg sarm.val.reverse main.val
  have outer := walkWeight_append_le G physical physical_nonneg (sarm.val.reverse.append main.val) tarm.val
  have erase := NodeMetric.toPath_weight_le G physical physical_nonneg ((sarm.val.reverse.append main.val).append tarm.val)
  have reverse_eq : NodeMetric.walkWeight G physical sarm.val.reverse = NodeMetric.walkWeight G physical sarm.val := by
    simp [NodeMetric.walkWeight, SimpleGraph.Walk.support_reverse]
  rw [reverse_eq] at inner
  linarith

theorem main_centers_distinct {buying physical : V → ℚ} {budget allowance : ℚ} {h ratio : ℕ}
    {s t u v : V} {reachable : Nonempty (G.Path s t)} {before first assigned : RoundingState G}
    {bornS bornT : Bool} {sarm : G.Path s u} {tarm : G.Path t v}
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (budget_pos : 0 < budget) (allowance_pos : 0 < allowance) (ratio_pos : 0 < ratio)
    (terminal_buying : buying s = 0 ∧ buying t = 0) (terminal_physical : physical s = 0 ∧ physical t = 0)
    (choice : MainChoice G buying physical before budget allowance h ratio s t reachable)
    (assignS : CenterAssignment G buying physical allowance (gridScale budget ratio choice.index) s before first bornS u sarm)
    (assignT : CenterAssignment G buying physical allowance (gridScale budget ratio choice.index) t first assigned bornT v tarm) : u ≠ v := by
  intro same
  subst v
  have hr : 0 < (ratio : ℚ) := by exact_mod_cast ratio_pos
  have scale_pos : 0 < gridScale budget ratio choice.index := by unfold gridScale; positivity
  have eligible := (Finset.mem_filter.mp choice.largest.1).2
  have s_short := CenterAssignment.arm_short G assignS terminal_buying.1 terminal_physical.1 scale_pos.le
  have back : first.bought ⊆ before.bought := by rw [assignS.bought_eq]
  have t_short := (mixed_walk_bought_mono G buying physical buying_nonneg first before back allowance _ tarm).trans
    (CenterAssignment.arm_short G assignT terminal_buying.2 terminal_physical.2 scale_pos.le)
  let weight := mixedNodeWeight G buying physical before allowance (gridScale budget ratio choice.index)
  have weight_nonneg := mixedWeight_nonneg G buying physical buying_nonneg physical_nonneg before allowance _ allowance_pos scale_pos.le
  have comparator := NodeMetric.distance_le_path G weight reachable (sarm.val.append tarm.val.reverse).toPath
  have erased := NodeMetric.toPath_weight_le G weight weight_nonneg (sarm.val.append tarm.val.reverse)
  have joined := walkWeight_append_le G weight weight_nonneg sarm.val tarm.val.reverse
  have reverse_eq : NodeMetric.walkWeight G weight tarm.val.reverse = NodeMetric.walkWeight G weight tarm.val := by
    simp [NodeMetric.walkWeight, SimpleGraph.Walk.support_reverse]
  rw [reverse_eq] at joined
  change NodeMetric.walkWeight G weight sarm.val ≤ _ at s_short
  change NodeMetric.walkWeight G weight tarm.val ≤ _ at t_short
  linarith

theorem main_realization_bought (state : RoundingState G) {s t u v : V}
    (sarm : G.Path s u) (main : G.Path s t) (tarm : G.Path t v) :
    ((sarm.val.reverse.append main.val).append tarm.val).toPath.val.support.toFinset ⊆
      (buyPath G (buyPath G (buyPath G state sarm) main) tarm).bought := by
  have s_bought := (path_bought_buyPath G state sarm).trans
    ((bought_subset_buyPath G (buyPath G state sarm) main).trans
      (bought_subset_buyPath G (buyPath G (buyPath G state sarm) main) tarm))
  have main_bought := (path_bought_buyPath G (buyPath G state sarm) main).trans
    (bought_subset_buyPath G (buyPath G (buyPath G state sarm) main) tarm)
  have t_bought := path_bought_buyPath G (buyPath G (buyPath G state sarm) main) tarm
  intro x hx
  have hx' : x ∈ ((sarm.val.reverse.append main.val).append tarm.val).toPath.val.support := by
    simpa only [List.mem_toFinset] using hx
  have original := ((sarm.val.reverse.append main.val).append tarm.val).support_toPath_subset_support hx'
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse, List.mem_reverse] at original
  rcases original with (hs | hm) | ht
  · exact s_bought (by simpa only [List.mem_toFinset] using hs)
  · exact main_bought (by simpa only [List.mem_toFinset] using hm)
  · exact t_bought (by simpa only [List.mem_toFinset] using ht)

/-- Strict form of all three source main-path inequalities (20). -/
theorem mainChoice_strict_path_bounds (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (state : RoundingState G) (budget allowance : ℚ) (h ratio : ℕ) (s t : V)
    (reachable : Nonempty (G.Path s t)) (budget_pos : 0 < budget) (allowance_pos : 0 < allowance) (ratio_pos : 0 < ratio)
    (top_ineligible : NodeMetric.distance G (mixedNodeWeight G buying physical state allowance (gridScale budget ratio 0)) s t reachable < gridScale budget ratio 0)
    (choice : MainChoice G buying physical state budget allowance h ratio s t reachable) :
    NodeMetric.walkWeight G (mixedNodeWeight G buying physical state allowance (gridScale budget ratio (choice.index-1))) choice.mainPath.val <
        gridScale budget ratio (choice.index-1) ∧
      residualWalkBuying G buying state choice.mainPath < (ratio : ℚ) * gridScale budget ratio choice.index ∧
      NodeMetric.walkWeight G physical choice.mainPath.val < allowance := by
  have ineligible := (largest_scale_predecessor_ineligible G buying physical state budget allowance h ratio s t reachable
    top_ineligible choice.index choice.largest).2.2
  have heq := shortest_weight_eq_distance G _ reachable choice.mainPath choice.shortest
  have mixed_short := heq.trans_lt ineligible
  have hr : (ratio : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ratio_pos)
  have scale_pos : 0 < gridScale budget ratio (choice.index-1) := by unfold gridScale; positivity
  have hd : choice.index = (choice.index-1)+1 := by have := choice.positive; omega
  have previous_eq : gridScale budget ratio (choice.index-1) = (ratio : ℚ) * gridScale budget ratio choice.index := by
    conv_rhs => rw [gridScale, hd, pow_succ]
    unfold gridScale
    field_simp
  have buying_short := (residualBuying_le_mixed G buying physical physical_nonneg state allowance _ allowance_pos scale_pos.le choice.mainPath).trans_lt mixed_short
  have physical_short := short_mixed_physical_bound_lt G buying physical buying_nonneg state allowance _ 1
    allowance_pos scale_pos (by norm_num) choice.mainPath (by simpa using mixed_short)
  exact ⟨mixed_short, by simpa only [previous_eq] using buying_short, by simpa using physical_short⟩

end BuyAtBulk.UpperBound
