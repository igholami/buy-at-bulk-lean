import BuyAtBulk.Computation.Rounding.MetadataLP
import BuyAtBulk.Computation.Rounding.ZeroBuying

/-! Correctness of the actual zero-physical preprocessing run and projection
of its stored paths, retaining their exact original physical length zero. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.Computation.Rounding
open BuyAtBulk.UpperBound
variable {V : Type} [Fintype V] [DecidableEq V] {n h : ℕ} {G : SimpleGraph V} [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)
local instance (physical : V → ℚ) : DecidableRel (zeroGraph G physical).Adj := zeroGraphDecidableAdj G physical

theorem projectZeroEntry_correct (physical : V → ℚ) (source target : Fin h → V) (lengths : Fin h → ℚ)
    (source_zero : ∀ i, physical (source i) = 0)
    (entry : Batch.RouteEntry (zeroGraph G physical) source (zeroTarget source target lengths))
    (zero : lengths entry.1 = 0) :
    ∃ path : G.Path (source entry.1) (target entry.1),
      projectZeroEntry G physical source target lengths entry = some ⟨entry.1, path⟩ ∧
      path.val.support = entry.2.val.support ∧ NodeMetric.walkWeight G physical path.val = 0 := by
  let path := ShortestPath.copyPath (projectZeroPath G physical entry.2) rfl
    (show zeroTarget source target lengths entry.1 = target entry.1 by simp only [zeroTarget, if_pos zero])
  refine ⟨path, by simp only [projectZeroEntry, dif_pos zero]; rfl, ?_, ?_⟩
  · simp only [path, ShortestPath.copyPath, SimpleGraph.Walk.support_copy, projectZeroPath_support]
  · rw [ShortestPath.copyPath_weight]
    exact projectZeroPath_physical_zero G physical entry.2 (source_zero entry.1)

theorem projectZeroEntries_indices (physical : V → ℚ) (source target : Fin h → V) (lengths : Fin h → ℚ)
    (entries : List (Batch.RouteEntry (zeroGraph G physical) source (zeroTarget source target lengths)))
    (all_zero : ∀ entry ∈ entries, lengths entry.1 = 0) :
    (projectZeroEntries G physical source target lengths entries).map (fun entry => entry.1) = entries.map (fun entry => entry.1) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    have zero := all_zero entry (List.mem_cons_self ..)
    have tail_zero : ∀ e ∈ entries, lengths e.1 = 0 := fun e he => all_zero e (List.mem_cons_of_mem _ he)
    simp only [projectZeroEntries, List.filterMap_cons, projectZeroEntry, dif_pos zero, List.map_cons]
    exact congrArg (fun tail => entry.1 :: tail) (ih tail_zero)

theorem projectZeroEntries_bounded (physical : V → ℚ) (source target : Fin h → V) (lengths : Fin h → ℚ)
    (source_zero : ∀ i, physical (source i) = 0) (bought : Finset V)
    (entries : List (Batch.RouteEntry (zeroGraph G physical) source (zeroTarget source target lengths)))
    (supported : ∀ entry ∈ entries, entry.2.val.support.toFinset ⊆ bought) :
    ∀ entry ∈ projectZeroEntries G physical source target lengths entries,
      entry.2.val.support.toFinset ⊆ bought ∧ NodeMetric.walkWeight G physical entry.2.val = 0 ∧ lengths entry.1 = 0 := by
  intro entry member
  obtain ⟨old, old_member, computed⟩ := List.mem_filterMap.mp member
  by_cases zero : lengths old.1 = 0
  · obtain ⟨path, returned, support, length⟩ := projectZeroEntry_correct physical source target lengths source_zero old zero
    have same := Option.some.inj (computed.symm.trans returned)
    subst entry
    exact ⟨by simpa only [support] using supported old old_member, length, zero⟩
  · simp only [projectZeroEntry, dif_neg zero] at computed
    contradiction

theorem restrictZeroState_buying_le (physical buying : V → ℚ) (nonnegative : ∀ v, 0 ≤ buying v)
    (state : RoundingState (zeroGraph G physical)) :
    nodeBuying buying (restrictZeroState G physical state).bought ≤ nodeBuying buying state.bought := by
  unfold nodeBuying restrictZeroState
  apply Finset.sum_le_sum
  intro v _
  by_cases member : v ∈ state.bought <;> by_cases zero : physical v = 0 <;>
    simp [member, zero, nonnegative v]

theorem zero_phase_correct (lp : NodeLP G h) (lengths : Fin h → ℚ)
    (metadata : ∀ i, lengths i = lp.fractionalLength i) (hh : 0 < h) (budget_pos : 0 < lp.buyingBudget) :
    ∃ after entries,
      zeroRun G numbering lp.buying lp.physical lp.opening lp.buyingBudget lp.source lp.target lengths = some (after, entries) ∧
      (nodeBuying lp.buying after.bought : ℝ) ≤ 490000 * binaryDepth h * lp.buyingBudget ∧
      entries.map (fun entry => entry.1) = CoreRun.requestOrder (zeroActive lengths) (fun _ => 1) ∧
      (∀ entry ∈ entries, entry.2.val.support.toFinset ⊆ after.bought) ∧
      ∀ entry ∈ projectZeroEntries G lp.physical lp.source lp.target lengths entries,
        entry.2.val.support.toFinset ⊆ after.bought ∧ NodeMetric.walkWeight G lp.physical entry.2.val = 0 ∧ lengths entry.1 = 0 := by
  letI := zeroGraphDecidableAdj G lp.physical
  by_cases empty : zeroActive lengths = ∅
  · refine ⟨⟨∅, [], []⟩, [], by simp [zeroRun, empty], ?_, ?_, by simp, ?_⟩
    · simp only [nodeBuying, Finset.notMem_empty, ite_false, Finset.sum_const_zero, Rat.cast_zero]
      have nonnegative : (0 : ℝ) ≤ lp.buyingBudget := by exact_mod_cast budget_pos.le
      positivity
    · simp [empty, CoreRun.requestOrder]
    · simp [projectZeroEntries]
  let zeroLP := zeroMetadataLP lp lengths metadata
  let B := restrictedBudget lp.buying lp.physical lp.opening
  have Bnonnegative : 0 ≤ B := restrictedBudget_nonneg lp
  have Ble : (B : ℝ) ≤ lp.buyingBudget := by exact_mod_cast restrictedBudget_le lp
  have raw : ∃ after entries,
      (if B = 0 then
        (freeRoutes (zeroGraph G lp.physical) numbering (fun _ => 0) lp.source
          (zeroTarget lp.source lp.target lengths) (fun _ => 0)
          (zeroState (zeroGraph G lp.physical) numbering lp.buying)
          (CoreRun.requestOrder (zeroActive lengths) (fun _ => 1))).map
            (fun entries => (zeroState (zeroGraph G lp.physical) numbering lp.buying, entries))
       else Core.run (zeroGraph G lp.physical) numbering lp.buying (fun _ => 0)
          (restrictedOpening lp.buying lp.physical lp.opening) B (fun _ : Fin h => 1)
          lp.source (zeroTarget lp.source lp.target lengths) (zeroActive lengths) 8 (binaryDepth h) ∅)
        = some (after, entries) ∧
      (nodeBuying lp.buying after.bought : ℝ) ≤ 490000 * binaryDepth h * lp.buyingBudget ∧
      entries.map (fun entry => entry.1) = CoreRun.requestOrder (zeroActive lengths) (fun _ => 1) ∧
      ∀ entry ∈ entries, entry.2.val.support.toFinset ⊆ after.bought := by
    by_cases zero : B = 0
    · have budget_zero : zeroLP.buyingBudget = 0 := by
        simpa only [zeroLP, zeroMetadataLP_buyingBudget] using zero
      have witness : ∀ i, HasShortBoughtRoute (zeroGraph G lp.physical) (fun _ => 0)
          (zeroState (zeroGraph G lp.physical) numbering lp.buying)
          (lp.source i) (zeroTarget lp.source lp.target lengths i) 0 := by
        intro i
        obtain ⟨path, positive, short⟩ := short_positive_path zeroLP i
        refine ⟨path, ?_, ?_⟩
        · intro v member
          apply (Core.mem_zeroBuyingNodes numbering lp.buying v).mpr
          exact positive_path_free zeroLP budget_zero i path positive v (List.mem_toFinset.mp member)
        · simp [NodeMetric.walkWeight]
      obtain ⟨entries, computed, indices, bounds⟩ := freeRoutes_correct numbering (fun _ => 0) (fun _ => le_rfl)
        lp.source (zeroTarget lp.source lp.target lengths) (fun _ => 0)
        (zeroState (zeroGraph G lp.physical) numbering lp.buying) witness
        (CoreRun.requestOrder (zeroActive lengths) (fun _ => 1))
      refine ⟨zeroState (zeroGraph G lp.physical) numbering lp.buying, entries, ?_, ?_, indices, ?_⟩
      · simp only [if_pos zero, computed, Option.map_some]
      · rw [zeroState_buying numbering]
        have nonnegative : (0 : ℝ) ≤ lp.buyingBudget := by exact_mod_cast budget_pos.le
        simp only [Rat.cast_zero]
        positivity
      · exact fun entry member => (bounds entry member).1
    · have zero_budget : 0 < zeroLP.buyingBudget := by
        rw [zeroMetadataLP_buyingBudget]
        exact lt_of_le_of_ne Bnonnegative (Ne.symm zero)
      have lengths_bound : ∀ i : Fin h, zeroLP.fractionalLength i ≤ (1 : ℚ) / 64 := by
        intro i
        rw [zeroMetadataLP_fractionalLength]
        norm_num
      obtain ⟨after, entries, computed, _, _, buying, indices, bounds, _⟩ :=
        Core.core_correct numbering zeroLP (fun _ => 1) (zeroActive lengths) 8 (binaryDepth h)
          zero_budget hh (by decide) (binaryDepth_pos h hh) (fun _ => by norm_num) lengths_bound ∅
      refine ⟨after, entries, ?_, ?_, indices, fun entry member => (bounds entry member).1⟩
      · have budget_eq : zeroLP.buyingBudget = B := rfl
        rw [budget_eq] at computed
        simpa only [if_neg zero, zeroLP, zeroMetadataLP] using computed
      · have factor := mul_le_mul_of_nonneg_right (zero_length_core_factor_bound h hh)
          (show (0 : ℝ) ≤ zeroLP.buyingBudget by exact_mod_cast zero_budget.le)
        have empty_cost : nodeBuying zeroLP.buying (∅ : Finset V) = 0 := by
          simp only [nodeBuying, Finset.notMem_empty, if_false, Finset.sum_const_zero]
        rw [empty_cost, Rat.cast_zero, zero_add, zeroMetadataLP_buyingBudget] at buying
        have first : (nodeBuying lp.buying after.bought : ℝ) ≤ 490000 * binaryDepth h * B :=
          buying.trans factor
        exact first.trans (mul_le_mul_of_nonneg_left Ble (by positivity))
  obtain ⟨after, entries, computed, buying, indices, supported⟩ := raw
  have restricted : ∀ entry ∈ entries,
      entry.2.val.support.toFinset ⊆ (restrictZeroState G lp.physical after).bought := by
    intro entry member v present
    apply Finset.mem_filter.mpr
    exact ⟨supported entry member present,
      zeroGraph_walk_nodes G lp.physical entry.2.val (lp.source_physical entry.1) v (List.mem_toFinset.mp present)⟩
  refine ⟨restrictZeroState G lp.physical after, entries, ?_, ?_, indices, restricted, ?_⟩
  · simp only [zeroRun, if_neg empty]
    dsimp only [B] at computed
    rw [computed]
    rfl
  · have le : (nodeBuying lp.buying (restrictZeroState G lp.physical after).bought : ℝ) ≤
        nodeBuying lp.buying after.bought := by
      exact_mod_cast restrictZeroState_buying_le lp.physical lp.buying lp.buying_nonneg after
    exact le.trans buying
  · exact projectZeroEntries_bounded lp.physical lp.source lp.target lengths lp.source_physical
      (restrictZeroState G lp.physical after).bought entries restricted

/-- Every successful zero-phase output excludes positive-physical resources,
even without feasibility assumptions on the numerical inputs. -/
theorem zeroRun_bought_zero (buying physical opening : V → ℚ) (budget : ℚ)
    (source target : Fin h → V) (lengths : Fin h → ℚ)
    (after : RoundingState (zeroGraph G physical))
    (entries : List (Batch.RouteEntry (zeroGraph G physical) source (zeroTarget source target lengths)))
    (computed : zeroRun G numbering buying physical opening budget source target lengths = some (after, entries))
    (v : V) (bought : v ∈ after.bought) : physical v = 0 := by
  unfold zeroRun at computed
  split at computed
  · have equal := Option.some.inj computed
    cases equal
    exact False.elim (Finset.notMem_empty v bought)
  · obtain ⟨result, _, same⟩ := Option.map_eq_some_iff.mp computed
    cases same
    exact (Finset.mem_filter.mp bought).2

/-- The unused slots of zero preprocessing are self-pairs, so only selected
zero-rental requests can contribute rows to its helper. -/
theorem zero_inactive_row_excluded (lp : NodeLP G h) (lengths : Fin h → ℚ)
    (raw : Core.RawRow h 8) (inactive : lengths raw.1 ≠ 0) :
    (Core.materializeRow (zeroGraph G lp.physical) numbering lp.buying (fun _ => 0)
      (restrictedBudget lp.buying lp.physical lp.opening) (fun _ => 1)
      lp.source (zeroTarget lp.source lp.target lengths) 8 raw).included = false := by
  letI := zeroGraphDecidableAdj G lp.physical
  have nonnegScale : 0 ≤ gridScale (restrictedBudget lp.buying lp.physical lp.opening) 8 raw.2.2 := by
    have budget_nonneg := restrictedBudget_nonneg lp
    unfold gridScale
    positivity
  have distance : Tolls.distanceTo (zeroGraph G lp.physical)
      (fun v => lp.buying v + (gridScale (restrictedBudget lp.buying lp.physical lp.opening) 8 raw.2.2 / 1) * 0)
      (lp.source raw.1) (lp.source raw.1) = 0 := by
    rw [Tolls.distanceTo_of_reachable _ _ (show Nonempty ((zeroGraph G lp.physical).Path (lp.source raw.1) (lp.source raw.1)) from ⟨SimpleGraph.Path.nil⟩),
      NodeMetric.distance_self _ _ (fun v => by simpa using lp.buying_nonneg v)]
    simp [lp.source_buying]
  have sides : Core.rowSource lp.source (zeroTarget lp.source lp.target lengths) raw.2.1 raw.1 = lp.source raw.1 ∧
      Core.rowMate lp.source (zeroTarget lp.source lp.target lengths) raw.2.1 raw.1 = lp.source raw.1 := by
    simp only [Core.rowSource, Core.rowMate, zeroTarget, if_neg inactive]
    cases raw.2.1 <;> simp
  have criterion := Core.materializeRow_included (zeroGraph G lp.physical) numbering lp.buying (fun _ => 0)
    lp.buying_nonneg (fun _ => le_rfl) (restrictedBudget lp.buying lp.physical lp.opening) (restrictedBudget_nonneg lp)
    (fun _ => 1) (fun _ => by norm_num) lp.source (zeroTarget lp.source lp.target lengths) 8 raw
  rw [sides.1, sides.2, distance] at criterion
  cases value : (Core.materializeRow (zeroGraph G lp.physical) numbering lp.buying (fun _ => 0)
      (restrictedBudget lp.buying lp.physical lp.opening) (fun _ => 1)
      lp.source (zeroTarget lp.source lp.target lengths) 8 raw).included with
  | false => rfl
  | true =>
    have impossible := criterion.mp value
    have nonnegative : 0 ≤ gridScale (restrictedBudget lp.buying lp.physical lp.opening) 8 raw.2.2 / 16 :=
      div_nonneg nonnegScale (by norm_num)
    exact False.elim (not_lt_of_ge nonnegative impossible)

end BuyAtBulk.Computation.Rounding
