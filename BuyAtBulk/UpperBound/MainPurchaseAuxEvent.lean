import BuyAtBulk.UpperBound.MainPurchaseBounds
import BuyAtBulk.UpperBound.AuxiliaryTrace
import BuyAtBulk.UpperBound.CenterBirthNew

/-! The actual main-purchase auxiliary event, with its source branch reason,
physical route, incremental cost, and distinct physical center endpoints. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

noncomputable def mainPurchaseEvent {buying physical : V → ℚ} {budget allowance : ℚ} {h ratio : ℕ}
    {s t : V} {reachable : Nonempty (G.Path s t)} (before first assigned : RoundingState G)
    (choice : MainChoice G buying physical before budget allowance h ratio s t reachable)
    {u v : V} (sarm : G.Path s u) (tarm : G.Path t v) (bornS bornT : Bool) : AuxiliaryEvent G :=
  let edge : AuxiliaryEdge G := ⟨u, v, gridScale budget ratio choice.index,
    ((sarm.val.reverse.append choice.mainPath.val).append tarm.val).toPath⟩
  ⟨edge, allowance, assigned,
    recordEdge G (buyPath G (buyPath G (buyPath G assigned sarm) choice.mainPath) tarm) edge.realization edge.scale,
    if bornS then some (u, before) else if bornT then some (v, first) else none⟩

theorem centerAssignment_noAuxiliaryProgress {buying physical : V → ℚ} {allowance scale : ℚ}
    {z center : V} {before after : RoundingState G} {born : Bool} {arm : G.Path z center}
    (assignment : CenterAssignment G buying physical allowance scale z before after born center arm) :
    NoAuxiliaryProgress G before after := by
  refine ⟨⟨?_, assignment.centers_preserved⟩, assignment.edges_eq⟩
  rw [assignment.bought_eq]

theorem mainPurchaseEvent_valid {buying physical : V → ℚ} {budget allowance thresholdFactor : ℚ} {h ratio : ℕ}
    {s t u v : V} {reachable : Nonempty (G.Path s t)} {before first assigned : RoundingState G}
    {bornS bornT : Bool} {sarm : G.Path s u} {tarm : G.Path t v}
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (budget_pos : 0 < budget) (allowance_pos : 0 < allowance) (ratio_pos : 0 < ratio)
    (terminal_buying : buying s = 0 ∧ buying t = 0) (terminal_physical : physical s = 0 ∧ physical t = 0)
    (top_ineligible : NodeMetric.distance G (mixedNodeWeight G buying physical before allowance (gridScale budget ratio 0)) s t reachable < gridScale budget ratio 0)
    (choice : MainChoice G buying physical before budget allowance h ratio s t reachable)
    (assignS : CenterAssignment G buying physical allowance (gridScale budget ratio choice.index) s before first bornS u sarm)
    (assignT : CenterAssignment G buying physical allowance (gridScale budget ratio choice.index) t first assigned bornT v tarm)
    (initial : EdgesEligible G before)
    (must_buy : bornS = true ∨ bornT = true ∨ ¬ HasShortBoughtRoute G physical assigned u v (thresholdFactor * allowance)) :
    let event := mainPurchaseEvent G before first assigned choice sarm tarm bornS bornT
    AuxiliaryGuard G physical thresholdFactor event ∧ AuxiliaryBounds G buying physical ratio event ∧ event.edge.source ≠ event.edge.target := by
  let event := mainPurchaseEvent G before first assigned choice sarm tarm bornS bornT
  have hr : 0 < (ratio : ℚ) := by exact_mod_cast ratio_pos
  have scale_pos : 0 < gridScale budget ratio choice.index := by unfold gridScale; positivity
  have first_eligible := edgesEligible_preserved G before first initial assignS.centers_preserved assignS.edges_eq
  have source_eligible := eligible_of_records_sublist first.centers assigned.centers assignT.centers_preserved
    u (gridScale budget ratio choice.index) assignS.eligible_after
  have s_physical := CenterAssignment.physical_arm_bound G assignS buying_nonneg allowance_pos scale_pos terminal_buying.1 terminal_physical.1
  have t_physical := CenterAssignment.physical_arm_bound G assignT buying_nonneg allowance_pos scale_pos terminal_buying.2 terminal_physical.2
  have main_physical := mainChoice_physical G buying physical buying_nonneg before budget allowance h ratio s t reachable
    budget_pos allowance_pos ratio_pos top_ineligible choice
  refine ⟨?_, ⟨allowance_pos, scale_pos, ?_, ?_⟩, ?_⟩
  · refine ⟨rfl, ⟨?_, List.Sublist.refl _⟩, main_realization_bought G assigned sarm choice.mainPath tarm,
      source_eligible, assignT.eligible_after, ?_⟩
    · exact (bought_subset_buyPath G assigned sarm).trans
        ((bought_subset_buyPath G (buyPath G assigned sarm) choice.mainPath).trans
          (bought_subset_buyPath G (buyPath G (buyPath G assigned sarm) choice.mainPath) tarm))
    · dsimp [mainPurchaseEvent]
      split_ifs with born_s born_t
      · have assignment := assignS
        rw [born_s] at assignment
        obtain ⟨center_eq, _, separated⟩ := CenterAssignment.birth_details G assignment
        refine ⟨Or.inl rfl, (assignT.edges_eq.trans assignS.edges_eq).symm, initial, ?_⟩
        simpa only [center_eq] using separated_center_new G buying physical before allowance _ s
          terminal_buying.1 terminal_physical.1 scale_pos.le separated
      · have assignment := assignT
        rw [born_t] at assignment
        obtain ⟨center_eq, _, separated⟩ := CenterAssignment.birth_details G assignment
        refine ⟨Or.inr rfl, assignT.edges_eq.symm, first_eligible, ?_⟩
        simpa only [center_eq] using separated_center_new G buying physical first allowance _ t
          terminal_buying.2 terminal_physical.2 scale_pos.le separated
      · rcases must_buy with hs | ht | no_bypass
        · exact False.elim (born_s hs)
        · exact False.elim (born_t ht)
        · exact no_bypass
  · exact (main_purchase_realization G physical physical_nonneg allowance allowance_pos sarm choice.mainPath tarm
      s_physical main_physical t_physical).le
  · exact main_purchase_buying G buying_nonneg physical_nonneg budget_pos allowance_pos ratio_pos terminal_buying terminal_physical
      top_ineligible choice assignS assignT
  · exact main_centers_distinct G buying_nonneg physical_nonneg budget_pos allowance_pos ratio_pos terminal_buying terminal_physical choice assignS assignT

end BuyAtBulk.UpperBound
