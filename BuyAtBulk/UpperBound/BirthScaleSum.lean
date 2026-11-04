import BuyAtBulk.UpperBound.RunPacking

/-! Summing actual chronological birth scales, with multiplicity, over the
`K` active grid positions. The bottom position at depth `K` is at or below
the cutoff, so it cannot create a birth. No conversion of repeated records
into a set is used. -/
noncomputable section
namespace BuyAtBulk.UpperBound

variable {I J : Type} [Fintype I] [Fintype J]

theorem sum_le_level_counts (level : J → ℚ) (level_nonneg : ∀ j, 0 ≤ level j)
    (value : I → ℚ) (covered : ∀ i, ∃ j, value i = level j) :
    (∑ i, value i) ≤ ∑ j, level j * Fintype.card {i : I // value i = level j} := by
  classical
  have count_eq (j : J) : (Fintype.card {i : I // value i = level j} : ℚ) =
      ∑ i, if value i = level j then (1 : ℚ) else 0 := by
    rw [Fintype.card_subtype]
    simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> norm_num
  simp_rw [count_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  obtain ⟨j, hj⟩ := covered i
  have nonneg : ∀ k ∈ (Finset.univ : Finset J), 0 ≤ level k * (if value i = level k then 1 else 0) := by
    intro k _
    split_ifs <;> simp [level_nonneg]
  have bound := Finset.single_le_sum nonneg (Finset.mem_univ j)
  simpa [hj] using bound

namespace NodeLP

variable {V : Type} [Fintype V] {G : SimpleGraph V} {h : ℕ}
local instance birthScaleSumLocalInst1 : DecidableEq V := Classical.decEq V
local instance birthScaleSumLocalInst2 : DecidableRel G.Adj := Classical.decRel _
variable (lp : NodeLP G h)

theorem run_birth_scale_sum (allowance : Fin h → ℚ) (ratio : ℕ)
    (budget_pos : 0 < lp.buyingBudget) (hh : 0 < h) (ratio_ge : 2 ≤ ratio)
    (allowance_pos : ∀ i, 0 < allowance i)
    (length_bound : ∀ i, lp.fractionalLength i ≤ allowance i / 64)
    (selection : Helper.Selection (lp.fixedTollData allowance ratio budget_pos ratio_ge allowance_pos length_bound) h)
    (thresholdFactor : ℚ) {order : List (Fin h)} {before after : RoundingState G}
    (execution : RunExec G lp.buying lp.physical lp.buyingBudget ratio thresholdFactor
      lp.source lp.target allowance order before after)
    (sorted : order.Pairwise fun i j => allowance i ≤ allowance j)
    (helper_bought : selection.nodes ⊆ before.bought) :
    ∃ events, BirthTrace G lp.buying lp.physical before events after ∧
      RunBirthMetadata lp.buyingBudget ratio lp.source lp.target allowance order events ∧
      (∑ i : Fin events.length, (events.get i).scale) ≤
        (1664 / 3 : ℚ) * (gridDepth h ratio) * lp.buyingBudget := by
  obtain ⟨events, trace, metadata, packed⟩ := lp.run_birth_packing allowance ratio budget_pos hh ratio_ge
    allowance_pos length_bound selection thresholdFactor execution sorted helper_bought
  refine ⟨events, trace, metadata, ?_⟩
  have covered : ∀ i : Fin events.length, ∃ depth : Fin (gridDepth h ratio),
      (events.get i).scale = gridScale lp.buyingBudget ratio depth := by
    intro i
    obtain ⟨_, _, _, _, depth, bound, scale_eq⟩ := metadata (events.get i) (List.get_mem ..)
    exact ⟨⟨depth, by omega⟩, scale_eq⟩
  have hsum := sum_le_level_counts (fun depth : Fin (gridDepth h ratio) =>
      gridScale lp.buyingBudget ratio depth)
    (fun depth => (lp.gridScale_pos budget_pos ratio ratio_ge depth).le)
    (fun i : Fin events.length => (events.get i).scale) covered
  calc
    _ ≤ ∑ depth : Fin (gridDepth h ratio), gridScale lp.buyingBudget ratio depth *
        Fintype.card (BirthsAtScale events (gridScale lp.buyingBudget ratio depth)) := hsum
    _ ≤ ∑ _ : Fin (gridDepth h ratio), (1664 / 3 : ℚ) * lp.buyingBudget :=
      Finset.sum_le_sum fun depth _ => packed ⟨depth, by omega⟩
    _ = _ := by simp; ring

end NodeLP
end BuyAtBulk.UpperBound
