import BuyAtBulk.Computation.Rounding.PositiveMetadata

/-! Positive requests use original flows; inactive slots are self-pairs and
have no included fixed helper rows. Empty positive phases return their seed. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.Computation.Rounding
open BuyAtBulk.UpperBound
variable {V : Type} [Fintype V] [DecidableEq V] {n h : ℕ} {G : SimpleGraph V} [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

theorem projectPositiveEntry_correct (source target : Fin h → V) (lengths : Fin h → ℚ)
    (physical : V → ℚ)
    (entry : Batch.RouteEntry G source (positiveTarget source target lengths))
    (positive : lengths entry.1 ≠ 0) :
    ∃ path : G.Path (source entry.1) (target entry.1),
      projectPositiveEntry G source target lengths entry = some ⟨entry.1, path⟩ ∧
      path.val.support = entry.2.val.support ∧
      NodeMetric.walkWeight G physical path.val = NodeMetric.walkWeight G physical entry.2.val := by
  let path := ShortestPath.copyPath entry.2 rfl
    (show positiveTarget source target lengths entry.1 = target entry.1 by simp [positiveTarget, positive])
  refine ⟨path, by simp only [projectPositiveEntry, dif_pos positive]; rfl, ?_, ?_⟩
  · simp [path, ShortestPath.copyPath]
  · exact ShortestPath.copyPath_weight physical entry.2 rfl _

theorem projectPositiveEntries_indices (source target : Fin h → V) (lengths : Fin h → ℚ)
    (entries : List (Batch.RouteEntry G source (positiveTarget source target lengths)))
    (all_positive : ∀ entry ∈ entries, lengths entry.1 ≠ 0) :
    (projectPositiveEntries G source target lengths entries).map (fun entry => entry.1) = entries.map (fun entry => entry.1) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    have positive := all_positive entry (List.mem_cons_self ..)
    have tail : ∀ e ∈ entries, lengths e.1 ≠ 0 := fun e he => all_positive e (List.mem_cons_of_mem _ he)
    simp only [projectPositiveEntries, List.filterMap_cons, projectPositiveEntry, dif_pos positive, List.map_cons]
    exact congrArg (fun rest => entry.1 :: rest) (ih tail)

theorem positiveRun_correct (lp : NodeLP G h) (lengths : Fin h → ℚ)
    (metadata : ∀ i, lengths i = lp.fractionalLength i) (ratio r : ℕ)
    (ratio_ge : 8 ≤ ratio) (r_ge : 1 ≤ r) (hh : 0 < h) (budget_pos : 0 < lp.buyingBudget)
    (seed : Finset V) :
    ∃ after entries,
      positiveRun G numbering lp.buying lp.physical lp.opening lp.buyingBudget lp.source lp.target lengths ratio r seed =
        some (after, entries) ∧
      seed ⊆ after.bought ∧
      (nodeBuying lp.buying after.bought : ℝ) ≤ (nodeBuying lp.buying seed : ℝ) +
        coreBuyingFactor h ratio r * lp.buyingBudget ∧
      entries.map (fun entry => entry.1) = CoreRun.requestOrder (positiveActive lengths) (allowance lengths) ∧
      ∀ entry ∈ entries, entry.2.val.support.toFinset ⊆ after.bought ∧
        NodeMetric.walkWeight G lp.physical entry.2.val ≤ coreRouteFactor h ratio r * allowance lengths entry.1 := by
  by_cases empty : positiveActive lengths = ∅
  · refine ⟨⟨seed, [], []⟩, [], by simp [positiveRun, empty], Finset.Subset.refl _, ?_, ?_, by simp⟩
    · apply le_add_of_nonneg_right
      have nonnegative : (0 : ℝ) ≤ lp.buyingBudget := by exact_mod_cast budget_pos.le
      have alpha_nonneg : (0 : ℝ) ≤ (Helper.TollData.alpha h : ℚ) := by
        unfold Helper.TollData.alpha
        positivity
      unfold coreBuyingFactor
      have ratio_nonneg : (0 : ℝ) ≤ ratio := Nat.cast_nonneg _
      have ratio_one : (1 : ℝ) ≤ ratio := by exact_mod_cast (show (1 : ℕ) ≤ ratio by omega)
      have denom_nonneg : (0 : ℝ) ≤ (ratio : ℝ) - 1 := by linarith
      positivity
    · simp [empty, CoreRun.requestOrder]
  let positiveLP := positiveMetadataLP lp lengths
  have lengths_nonneg : ∀ i, 0 ≤ lengths i := fun i => by rw [metadata i]; exact lp.fractionalLength_nonneg i
  have allowance_pos : ∀ i, 0 < allowance lengths i := by
    intro i
    dsimp [allowance]
    split_ifs with zero
    · norm_num
    · have positive : 0 < lengths i := lt_of_le_of_ne (lengths_nonneg i) (Ne.symm zero)
      positivity
  have allowance_bound : ∀ i, positiveLP.fractionalLength i ≤ allowance lengths i / 64 := by
    intro i
    rw [positiveMetadataLP_fractionalLength]
    dsimp [allowance]
    split_ifs with zero
    · norm_num
    · rw [← metadata i]
      linarith
  obtain ⟨after, entries, computed, _, retained, buying, indices, bounds, _⟩ :=
    Core.core_correct numbering positiveLP (allowance lengths) (positiveActive lengths) ratio r
      budget_pos hh ratio_ge r_ge allowance_pos allowance_bound seed
  have positive_only : ∀ entry ∈ entries, lengths entry.1 ≠ 0 := by
    intro entry member
    have in_order : entry.1 ∈ entries.map (fun e => e.1) := List.mem_map.mpr ⟨entry, member, rfl⟩
    rw [indices] at in_order
    exact (Finset.mem_filter.mp ((CoreRun.mem_requestOrder _ _ _).mp in_order)).2
  refine ⟨after, projectPositiveEntries G lp.source lp.target lengths entries, ?_, retained, buying, ?_, ?_⟩
  · simp only [positiveRun, if_neg empty]
    change Core.run G numbering lp.buying lp.physical lp.opening lp.buyingBudget (allowance lengths) lp.source
        (positiveTarget lp.source lp.target lengths) (positiveActive lengths) ratio r seed = some (after, entries) at computed
    rw [computed]
    rfl
  · exact (projectPositiveEntries_indices lp.source lp.target lengths entries positive_only).trans indices
  · intro entry member
    obtain ⟨old, old_member, returned⟩ := List.mem_filterMap.mp member
    obtain ⟨path, projected, support, weight⟩ := projectPositiveEntry_correct lp.source lp.target lengths lp.physical
      old (positive_only old old_member)
    have same := Option.some.inj (returned.symm.trans projected)
    subst entry
    obtain ⟨supported, bounded⟩ := bounds old old_member
    exact ⟨by simpa only [support] using supported, weight.trans_le bounded⟩

/-- Dummy self-pairs contribute no rows to the helper's actual included list. -/
theorem positive_inactive_row_excluded (lp : NodeLP G h) (lengths : Fin h → ℚ)
    (ratio : ℕ) (raw : Core.RawRow h ratio) (inactive : lengths raw.1 = 0)
    (allowance_pos : ∀ i, 0 < allowance lengths i) :
    (Core.materializeRow G numbering lp.buying lp.physical lp.buyingBudget (allowance lengths)
      lp.source (positiveTarget lp.source lp.target lengths) ratio raw).included = false := by
  have nonnegScale : 0 ≤ gridScale lp.buyingBudget ratio raw.2.2 := by
    have budget_nonneg := lp.buyingBudget_nonneg
    unfold gridScale
    positivity
  have coefficient : 0 ≤ gridScale lp.buyingBudget ratio raw.2.2 / allowance lengths raw.1 :=
    div_nonneg nonnegScale (allowance_pos raw.1).le
  have distance : Tolls.distanceTo G
      (fun v => lp.buying v + (gridScale lp.buyingBudget ratio raw.2.2 / allowance lengths raw.1) * lp.physical v)
      (lp.source raw.1) (lp.source raw.1) = 0 := by
    rw [Tolls.distanceTo_of_reachable G _ (show Nonempty (G.Path (lp.source raw.1) (lp.source raw.1)) from ⟨SimpleGraph.Path.nil⟩),
      NodeMetric.distance_self G _ (fun v => add_nonneg (lp.buying_nonneg v) (mul_nonneg coefficient (lp.physical_nonneg v)))]
    simp [lp.source_buying, lp.source_physical]
  have sides : Core.rowSource lp.source (positiveTarget lp.source lp.target lengths) raw.2.1 raw.1 = lp.source raw.1 ∧
      Core.rowMate lp.source (positiveTarget lp.source lp.target lengths) raw.2.1 raw.1 = lp.source raw.1 := by
    simp only [Core.rowSource, Core.rowMate, positiveTarget, if_pos inactive]
    cases raw.2.1 <;> simp
  have criterion := Core.materializeRow_included G numbering lp.buying lp.physical lp.buying_nonneg lp.physical_nonneg
    lp.buyingBudget lp.buyingBudget_nonneg (allowance lengths) allowance_pos lp.source
    (positiveTarget lp.source lp.target lengths) ratio raw
  rw [sides.1, sides.2, distance] at criterion
  cases value : (Core.materializeRow G numbering lp.buying lp.physical lp.buyingBudget (allowance lengths)
      lp.source (positiveTarget lp.source lp.target lengths) ratio raw).included with
  | false => rfl
  | true =>
    have impossible := criterion.mp value
    have nonnegative : 0 ≤ gridScale lp.buyingBudget ratio raw.2.2 / 16 := div_nonneg nonnegScale (by norm_num)
    exact False.elim (not_lt_of_ge nonnegative impossible)

end BuyAtBulk.Computation.Rounding
