import BuyAtBulk.Computation.Serve.ReuseRefinement

/-! Every feasible original request has an actual deterministic computed main
result, and that exact result realizes the source main operational relation. -/
namespace BuyAtBulk.Computation.Serve
open BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

private theorem false_flags (a b : Bool) (not_born : ¬ (a || b) = true) : a = false ∧ b = false := by
  cases a <;> cases b <;> simp_all

theorem run_refines (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (budget allowance : ℚ) (h ratio : ℕ) (threshold : ℚ)
    (budget_nonneg : 0 ≤ budget) (allowance_pos : 0 < allowance) (h_pos : 0 < h) (ratio_ge : 2 ≤ ratio)
    (s t : V) (reachable : Nonempty (G.Path s t)) (state : RoundingState G)
    (top_ineligible : NodeMetric.distance G
      (mixedNodeWeight G buying physical state allowance (gridScale budget ratio 0)) s t reachable < gridScale budget ratio 0) :
    ∃ final route, run G numbering buying physical budget allowance h ratio threshold s t state = some (final, route) ∧
      ServeExec G buying physical budget allowance h ratio threshold s t reachable state final route := by
  have ratio_pos : (0 : ℚ) < ratio := by exact_mod_cast (show 0 < ratio by omega)
  have nonneg_at : ∀ d, ∀ v, 0 ≤ Attachment.mixedWeight G buying physical state allowance (gridScale budget ratio d) v :=
    fun d => Attachment.mixedWeight_nonneg G buying physical buying_nonneg physical_nonneg state allowance _ allowance_pos
      (scale_nonneg budget budget_nonneg ratio d)
  cases bought_eq : Attachment.boughtRoute G numbering physical state s t allowance with
  | some route =>
    have facts := Attachment.boughtRoute_some G numbering physical physical_nonneg state route bought_eq
    have shortest : IsShortestBought G physical state route :=
      ⟨facts.1, Attachment.boughtRoute_shortest G numbering physical physical_nonneg state route bought_eq⟩
    exact ⟨state, route, by simp only [run, bought_eq], ServeExec.already_bought state route shortest facts.2⟩
  | none =>
    have not_bought := (Attachment.boughtRoute_none_iff G numbering physical physical_nonneg state s t allowance).mp bought_eq
    cases selected : selectScale G numbering buying physical state budget allowance h ratio s t with
    | none =>
      have empty := selectScale_none G numbering buying physical buying_nonneg physical_nonneg state budget allowance budget_nonneg allowance_pos h ratio s t reachable selected
      obtain ⟨route, computed, _, _⟩ := ShortestPath.indexed_shortest_path G
        (Attachment.mixedWeight G buying physical state allowance (gridScale budget ratio (gridDepth h ratio)))
        (nonneg_at _) numbering s t reachable
      have shortest := Attachment.shortestPath_shortest G numbering _ (nonneg_at _) route computed
      rw [Attachment.mixedWeight_eq] at shortest
      refine ⟨Attachment.purchase G state route, route, ?_, ?_⟩
      · simp only [run, bought_eq, selected, computed]
      · simpa only [Attachment.purchase_eq] using ServeExec.no_eligible state route not_bought empty shortest
    | some d =>
      have largest := selectScale_some G numbering buying physical buying_nonneg physical_nonneg state budget allowance budget_nonneg allowance_pos h ratio s t reachable d selected
      have positive := (largest_scale_predecessor_ineligible G buying physical state budget allowance h ratio s t reachable top_ineligible d largest).1
      obtain ⟨main, computed, _, _⟩ := ShortestPath.indexed_shortest_path G
        (Attachment.mixedWeight G buying physical state allowance (gridScale budget ratio (d - 1)))
        (nonneg_at _) numbering s t reachable
      have shortest := Attachment.shortestPath_shortest G numbering _ (nonneg_at _) main computed
      rw [Attachment.mixedWeight_eq] at shortest
      let choice : MainChoice G buying physical state budget allowance h ratio s t reachable := ⟨d, positive, largest, main, shortest⟩
      by_cases small : gridScale budget ratio d ≤ cutoff budget h ratio
      · refine ⟨Attachment.purchase G state main, main, ?_, ?_⟩
        · simp only [run, bought_eq, selected, computed, if_pos small]
        · simpa only [choice, Attachment.purchase_eq] using ServeExec.cheap state not_bought choice small
      have above : cutoff budget h ratio < gridScale budget ratio d := lt_of_not_ge small
      let first := assignCenter G numbering buying physical allowance (gridScale budget ratio d) s state
      let second := assignCenter G numbering buying physical allowance (gridScale budget ratio d) t first.state
      have assignS := assignCenter_refines G numbering buying physical buying_nonneg physical_nonneg allowance _ allowance_pos
        (scale_nonneg budget budget_nonneg ratio d) s state
      have assignT := assignCenter_refines G numbering buying physical buying_nonneg physical_nonneg allowance _ allowance_pos
        (scale_nonneg budget budget_nonneg ratio d) t first.state
      change CenterAssignment G buying physical allowance (gridScale budget ratio d) s state first.state first.born first.center first.arm at assignS
      change CenterAssignment G buying physical allowance (gridScale budget ratio d) t first.state second.state second.born second.center second.arm at assignT
      have purchase_exec (must_buy : first.born = true ∨ second.born = true ∨
          ¬ HasShortBoughtRoute G physical second.state first.center second.center threshold) :
          ServeExec G buying physical budget allowance h ratio threshold s t reachable state
            (purchaseMain G second.state first.arm main second.arm (gridScale budget ratio d)) main := by
        simpa only [purchaseMain, Attachment.purchase_eq, choice] using
          ServeExec.purchase state first.state second.state first.center second.center first.arm second.arm first.born second.born
            not_bought choice above assignS assignT must_buy
      by_cases born : (first.born || second.born) = true
      · refine ⟨purchaseMain G second.state first.arm main second.arm (gridScale budget ratio d), main, ?_, ?_⟩
        · dsimp only [first, second] at born
          simp only [run, bought_eq, selected, computed, if_neg small, if_pos born]
          rfl
        · rcases Bool.or_eq_true_iff.mp born with left | right
          · exact purchase_exec (Or.inl left)
          · exact purchase_exec (Or.inr (Or.inl right))
      obtain ⟨falseS, falseT⟩ := false_flags first.born second.born born
      cases bypass_eq : Attachment.boughtRoute G numbering physical second.state first.center second.center threshold with
      | none =>
        have missing := (Attachment.boughtRoute_none_iff G numbering physical physical_nonneg second.state first.center second.center threshold).mp bypass_eq
        refine ⟨purchaseMain G second.state first.arm main second.arm (gridScale budget ratio d), main, ?_, purchase_exec (Or.inr (Or.inr missing))⟩
        dsimp only [first, second] at born bypass_eq
        simp only [run, bought_eq, selected, computed, if_neg small, if_neg born, bypass_eq]
        rfl
      | some middle =>
        have facts := Attachment.boughtRoute_some G numbering physical physical_nonneg second.state middle bypass_eq
        rw [falseS] at assignS
        rw [falseT] at assignT
        let result := reuseArms G numbering buying physical budget allowance h ratio threshold (gridScale budget ratio d)
          s t first.center second.center first.arm second.arm middle second.state
        refine ⟨result.1, result.2, ?_, ?_⟩
        · dsimp only [first, second] at born bypass_eq
          simp only [run, bought_eq, selected, computed, if_neg small, if_neg born, bypass_eq]
          rfl
        · exact reuseArms_refines G numbering buying physical buying_nonneg physical_nonneg budget allowance h ratio threshold
            allowance_pos ratio_pos s t reachable state first.state second.state first.center second.center first.arm second.arm middle
            not_bought choice above assignS assignT facts.1 facts.2
            (div_nonneg (scale_nonneg budget budget_nonneg ratio d) ratio_pos.le)
            (grid_deadline budget h ratio d budget_nonneg h_pos ratio_ge)

end BuyAtBulk.Computation.Serve
