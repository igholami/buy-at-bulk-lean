import BuyAtBulk.Computation.CompactRounding

/-! The proved graph rounder accepts compact rational LP flows through the
computed sparse path-extraction transform and actual two-phase program.
No polynomial optimizer or complete runtime bound is asserted. -/
noncomputable section
namespace BuyAtBulk.CompactFlow.Solution
variable {V : Type} [Fintype V] {G : SimpleGraph V} {h : ℕ}
local instance compactFlowRoundingDecEq : DecidableEq V := Classical.decEq _
local instance compactFlowRoundingDecRel : DecidableRel G.Adj := Classical.decRel _

/-- Separate-budget rounding of an actual feasible compact node-split flow. -/
theorem rounding (f : Solution G h) {n : ℕ} (numbering : V ≃ Fin n) (ratio r : ℕ) (hratio : 8 ≤ ratio) (hr : 1 ≤ r)
    (hpos : 0 < h) (budgetpos : 0 < f.buyingBudget) :
    ∃ bought : Finset V,
      (UpperBound.nodeBuying f.buying bought : ℝ) ≤
        500000 * Statements.buyingFactor h ratio r * f.buyingBudget ∧
      ∃ paths : ∀ i, G.Path (f.source i) (f.target i),
        (∀ i, (paths i).val.support.toFinset ⊆ bought) ∧
        ((∑ i, f.demand i * NodeMetric.walkWeight G f.physical (paths i).val : ℚ) : ℝ) ≤
          500000 * ((r : ℝ) * Statements.gridLevels h ratio) * f.rentalBudget := by
  obtain ⟨output, _, hb, _, indices, bounds⟩ :=
    Computation.CompactRounding.run_correct G numbering f ratio r hratio hr
  have routes : ∀ i, ∃ path : G.Path (f.source i) (f.target i),
      path.val.support.toFinset ⊆ output.bought ∧
      NodeMetric.walkWeight G f.physical path.val ≤
        (500000 * r * UpperBound.gridDepth h ratio : ℚ) * f.fractionalLength i := by
    intro i
    have member : i ∈ output.routes.map (fun entry => entry.1) :=
      indices.mem_iff.mpr (List.mem_finRange i)
    obtain ⟨⟨j, path⟩, member, equal⟩ := List.mem_map.mp member
    dsimp only at equal
    subst j
    exact ⟨path, bounds ⟨i, path⟩ member⟩
  choose paths supported bounded using routes
  refine ⟨output.bought, hb, paths, supported, ?_⟩
  have rental : (∑ i, f.demand i * NodeMetric.walkWeight G f.physical (paths i).val : ℚ) ≤
      (500000 * r * UpperBound.gridDepth h ratio : ℚ) * f.rentalBudget := by
    calc
      _ ≤ ∑ i, f.demand i * ((500000 * r * UpperBound.gridDepth h ratio : ℚ) * f.fractionalLength i) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (bounded i) (f.demand_pos i).le
      _ = _ := by simp only [rentalBudget, Finset.mul_sum]; congr 1; funext i; ring
  have realRental : ((∑ i, f.demand i * NodeMetric.walkWeight G f.physical (paths i).val : ℚ) : ℝ) ≤
      ((500000 * r * UpperBound.gridDepth h ratio : ℚ) : ℝ) * f.rentalBudget := by exact_mod_cast rental
  simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat, UpperBound.gridDepth_eq_gridLevels, mul_assoc] using realRental

end BuyAtBulk.CompactFlow.Solution
