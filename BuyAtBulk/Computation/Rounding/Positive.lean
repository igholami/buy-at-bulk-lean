import BuyAtBulk.Computation.Rounding.ZeroPhase
import BuyAtBulk.Computation.Rounding.PositivePhase
import BuyAtBulk.Computation.Rounding.Accounting

/-! The actual positive-budget two-phase output. Stored zero routes project
with length zero and persist through the later original-graph core run. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.Computation.Rounding
open BuyAtBulk.UpperBound
variable {V : Type} [Fintype V] [DecidableEq V] {n h : ℕ} {G : SimpleGraph V} [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

theorem positive_correct (lp : NodeLP G h) (lengths : Fin h → ℚ)
    (metadata : ∀ i, lengths i = lp.fractionalLength i) (ratio r : ℕ)
    (ratio_ge : 8 ≤ ratio) (r_ge : 1 ≤ r) (hh : 0 < h) (budget_pos : 0 < lp.buyingBudget) :
    ∃ output,
      run G numbering lp.buying lp.physical lp.opening lp.buyingBudget lp.source lp.target lengths ratio r = some output ∧
      (nodeBuying lp.buying output.bought : ℝ) ≤ 500000 * Statements.buyingFactor h ratio r * lp.buyingBudget ∧
      (output.routes.map fun entry => entry.1).Perm (List.finRange h) ∧
      ∀ entry ∈ output.routes, entry.2.val.support.toFinset ⊆ output.bought ∧
        NodeMetric.walkWeight G lp.physical entry.2.val ≤
          (64 * coreRouteFactor h ratio r) * lp.fractionalLength entry.1 := by
  obtain ⟨zeroAfter, zeroEntries, zero_computed, zero_buying, zero_indices, zero_supported, zero_bounds⟩ :=
    zero_phase_correct numbering lp lengths metadata hh budget_pos
  obtain ⟨after, entries, computed, retained, buying, indices, bounds⟩ :=
    positiveRun_correct numbering lp lengths metadata ratio r ratio_ge r_ge hh budget_pos zeroAfter.bought
  have binary_le : (binaryDepth h : ℝ) ≤ Statements.buyingFactor h ratio r := by
    rw [binaryDepth_eq_binaryLevels]
    unfold Statements.buyingFactor
    exact le_add_of_nonneg_right (by positivity)
  have budget_nonneg : (0 : ℝ) ≤ lp.buyingBudget := by exact_mod_cast budget_pos.le
  have core_factor := coreBuyingFactor_le h ratio r hh ratio_ge
  have total_buying : (nodeBuying lp.buying after.bought : ℝ) ≤
      500000 * Statements.buyingFactor h ratio r * lp.buyingBudget := by
    have zero_factor := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left binary_le
      (by norm_num : (0 : ℝ) ≤ 490000)) budget_nonneg
    have positive_factor := mul_le_mul_of_nonneg_right core_factor budget_nonneg
    nlinarith
  have zero_only : ∀ entry ∈ zeroEntries, lengths entry.1 = 0 := by
    intro entry member
    have in_order : entry.1 ∈ zeroEntries.map (fun e => e.1) := List.mem_map.mpr ⟨entry, member, rfl⟩
    rw [zero_indices] at in_order
    exact (Finset.mem_filter.mp ((CoreRun.mem_requestOrder _ _ _).mp in_order)).2
  have projected_indices := projectZeroEntries_indices lp.physical lp.source lp.target lengths zeroEntries zero_only
  let allEntries := projectZeroEntries G lp.physical lp.source lp.target lengths zeroEntries ++ entries
  have permuted : (allEntries.map fun entry => entry.1).Perm (List.finRange h) := by
    simpa only [allEntries, List.map_append, projected_indices, zero_indices, indices] using phase_orders_perm lengths ratio
  refine ⟨⟨after.bought, allEntries⟩, ?_, total_buying, permuted, ?_⟩
  · simp only [run, if_neg (Nat.ne_of_gt hh), if_neg (ne_of_gt budget_pos), zero_computed, computed]
    rfl
  · intro entry member
    rcases List.mem_append.mp member with old | current
    · obtain ⟨supported, physical_zero, length_zero⟩ := zero_bounds entry old
      refine ⟨supported.trans retained, ?_⟩
      rw [physical_zero, ← metadata entry.1, length_zero, mul_zero]
    · obtain ⟨supported, bounded⟩ := bounds entry current
      have in_order : entry.1 ∈ entries.map (fun e => e.1) := List.mem_map.mpr ⟨entry, current, rfl⟩
      rw [indices] at in_order
      have positive : lengths entry.1 ≠ 0 := (Finset.mem_filter.mp ((CoreRun.mem_requestOrder _ _ _).mp in_order)).2
      refine ⟨supported, ?_⟩
      rw [allowance, if_neg positive, metadata entry.1] at bounded
      exact bounded.trans_eq (by ring)

end BuyAtBulk.Computation.Rounding
