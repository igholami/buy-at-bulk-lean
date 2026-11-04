import BuyAtBulk.Computation.Rounding.Positive
import BuyAtBulk.Computation.Rounding.ZeroBuying

/-! Full correctness of the numerical rounding program, including empty
instances and zero buying budget. Costs refer to the paths actually returned. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.Computation.Rounding
open BuyAtBulk.UpperBound
variable {V : Type} [Fintype V] [DecidableEq V] {n h : ℕ} {G : SimpleGraph V} [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

theorem run_routes_correct (lp : NodeLP G h) (lengths : Fin h → ℚ)
    (metadata : ∀ i, lengths i = lp.fractionalLength i) (ratio r : ℕ)
    (ratio_ge : 8 ≤ ratio) (r_ge : 1 ≤ r) :
    ∃ output,
      run G numbering lp.buying lp.physical lp.opening lp.buyingBudget lp.source lp.target lengths ratio r = some output ∧
      (nodeBuying lp.buying output.bought : ℝ) ≤ 500000 * Statements.buyingFactor h ratio r * lp.buyingBudget ∧
      (output.routes.map fun entry => entry.1).Perm (List.finRange h) ∧
      ∀ entry ∈ output.routes, entry.2.val.support.toFinset ⊆ output.bought ∧
        NodeMetric.walkWeight G lp.physical entry.2.val ≤
          (500000 * r * gridDepth h ratio : ℚ) * lp.fractionalLength entry.1 := by
  by_cases empty : h = 0
  · subst h
    refine ⟨⟨∅, []⟩, by simp [run], ?_, by simp, by simp⟩
    have budget_nonneg : (0 : ℝ) ≤ lp.buyingBudget := by exact_mod_cast lp.buyingBudget_nonneg
    change (nodeBuying lp.buying ∅ : ℝ) ≤ _
    simp only [nodeBuying, Finset.notMem_empty, ite_false, Finset.sum_const_zero, Rat.cast_zero]
    unfold Statements.buyingFactor
    positivity
  have hh : 0 < h := Nat.pos_of_ne_zero empty
  have grid_one : (1 : ℚ) ≤ gridDepth h ratio := by
    exact_mod_cast gridDepth_pos h ratio hh (by omega)
  have r_one : (1 : ℚ) ≤ r := by exact_mod_cast r_ge
  have product_one : (1 : ℚ) ≤ r * gridDepth h ratio := by
    nlinarith [mul_nonneg (sub_nonneg.mpr r_one) (sub_nonneg.mpr grid_one)]
  have coefficient_one : (1 : ℚ) ≤ 500000 * r * gridDepth h ratio := by nlinarith
  by_cases zero : lp.buyingBudget = 0
  · obtain ⟨entries, computed, indices, bounds⟩ := zero_budget_routes numbering lp zero lengths metadata
    refine ⟨⟨(zeroState G numbering lp.buying).bought, entries⟩, ?_, ?_, indices ▸ List.Perm.refl _, ?_⟩
    · simp only [run, if_neg empty, if_pos zero, computed, Option.map_some]
    · rw [zeroState_buying numbering, zero]
      simp
    · intro entry member
      obtain ⟨supported, bounded⟩ := bounds entry member
      exact ⟨supported, bounded.trans (by nlinarith [lp.fractionalLength_nonneg entry.1])⟩
  · have budget_pos : 0 < lp.buyingBudget := lt_of_le_of_ne lp.buyingBudget_nonneg (Ne.symm zero)
    obtain ⟨output, computed, buying, indices, bounds⟩ := positive_correct numbering lp lengths metadata ratio r ratio_ge r_ge hh budget_pos
    refine ⟨output, computed, buying, indices, ?_⟩
    have route_factor := coreRouteFactor_bound h ratio r hh (by omega) r_ge
    have coefficient : (64 * coreRouteFactor h ratio r : ℚ) ≤ 500000 * r * gridDepth h ratio := by
      nlinarith
    intro entry member
    obtain ⟨supported, bounded⟩ := bounds entry member
    exact ⟨supported, bounded.trans (mul_le_mul_of_nonneg_right coefficient (lp.fractionalLength_nonneg entry.1))⟩

end BuyAtBulk.Computation.Rounding
