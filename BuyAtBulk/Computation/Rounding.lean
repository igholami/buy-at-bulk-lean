import BuyAtBulk.Computation.Rounding.Refinement

/-! Executable two-phase node-LP rounding. The data program takes rational
length metadata, rather than an LP's exponentially indexed path flows. -/
noncomputable section
namespace BuyAtBulk.Computation.Rounding
open BuyAtBulk.UpperBound
variable {V : Type} [Fintype V] [DecidableEq V] {n h : ℕ} {G : SimpleGraph V} [DecidableRel G.Adj]


theorem run_correct (numbering : V ≃ Fin n) (lp : NodeLP G h) (lengths : Fin h → ℚ)
    (metadata : ∀ i, lengths i = lp.fractionalLength i) (ratio r : ℕ)
    (ratio_ge : 8 ≤ ratio) (r_ge : 1 ≤ r) :
    ∃ output,
      run G numbering lp.buying lp.physical lp.opening lp.buyingBudget lp.source lp.target lengths ratio r = some output ∧
      (nodeBuying lp.buying output.bought : ℝ) ≤ 500000 * Statements.buyingFactor h ratio r * lp.buyingBudget ∧
      (rentalCost lp.physical lp.demand output.routes : ℝ) ≤
        500000 * ((r : ℝ) * Statements.gridLevels h ratio) * lp.rentalBudget ∧
      (output.routes.map fun entry => entry.1).Perm (List.finRange h) ∧
      ∀ entry ∈ output.routes, entry.2.val.support.toFinset ⊆ output.bought ∧
        NodeMetric.walkWeight G lp.physical entry.2.val ≤
          (500000 * r * gridDepth h ratio : ℚ) * lp.fractionalLength entry.1 := by
  obtain ⟨output, computed, buying, indices, bounds⟩ := run_routes_correct numbering lp lengths metadata ratio r ratio_ge r_ge
  refine ⟨output, computed, buying, ?_, indices, bounds⟩
  have rental := rentalCost_le lp.physical lp.demand lp.fractionalLength (fun i => (lp.demand_pos i).le)
    output.routes indices (500000 * r * gridDepth h ratio) (fun entry member => (bounds entry member).2)
  have real_rental : (rentalCost lp.physical lp.demand output.routes : ℝ) ≤
      ((500000 * r * gridDepth h ratio : ℚ) : ℝ) * lp.rentalBudget := by exact_mod_cast rental
  simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat, gridDepth_eq_gridLevels, mul_assoc] using real_rental


/-- The actual program succeeds, returns each request once, and satisfies
both separate-budget bounds on the paths stored in its result. -/
theorem rounding_correct (numbering : V ≃ Fin n) (lp : NodeLP G h) (lengths : Fin h → ℚ)
    (metadata : ∀ i, lengths i = lp.fractionalLength i) (ratio r : ℕ)
    (ratio_ge : 8 ≤ ratio) (r_ge : 1 ≤ r) :
    ∃ output,
      run G numbering lp.buying lp.physical lp.opening lp.buyingBudget lp.source lp.target lengths ratio r = some output ∧
      (nodeBuying lp.buying output.bought : ℝ) ≤ 500000 * Statements.buyingFactor h ratio r * lp.buyingBudget ∧
      (rentalCost lp.physical lp.demand output.routes : ℝ) ≤
        500000 * ((r : ℝ) * Statements.gridLevels h ratio) * lp.rentalBudget ∧
      (output.routes.map fun entry => entry.1).Perm (List.finRange h) ∧
      ∀ i, ∃ path : G.Path (lp.source i) (lp.target i),
        (⟨i, path⟩ : Batch.RouteEntry G lp.source lp.target) ∈ output.routes ∧
        path.val.support.toFinset ⊆ output.bought ∧
        NodeMetric.walkWeight G lp.physical path.val ≤
          (500000 * r * gridDepth h ratio : ℚ) * lp.fractionalLength i := by
  obtain ⟨output, computed, buying, rental, indices, bounds⟩ := run_correct numbering lp lengths metadata ratio r ratio_ge r_ge
  refine ⟨output, computed, buying, rental, indices, ?_⟩
  intro i
  have member : i ∈ output.routes.map (fun entry => entry.1) := indices.mem_iff.mpr (List.mem_finRange i)
  obtain ⟨⟨j, path⟩, member, equal⟩ := List.mem_map.mp member
  dsimp only at equal
  subst j
  exact ⟨path, member, bounds ⟨i, path⟩ member⟩

/-- A conventional family-of-paths presentation, extracted from the actual
output. Every selected path is one of the program's stored entries. -/
theorem rounding_paths (numbering : V ≃ Fin n) (lp : NodeLP G h) (ratio r : ℕ)
    (ratio_ge : 8 ≤ ratio) (r_ge : 1 ≤ r) :
    ∃ bought : Finset V,
      (nodeBuying lp.buying bought : ℝ) ≤ 500000 * Statements.buyingFactor h ratio r * lp.buyingBudget ∧
      ∃ paths : ∀ i, G.Path (lp.source i) (lp.target i),
        (∀ i, (paths i).val.support.toFinset ⊆ bought) ∧
        ((∑ i, lp.demand i * NodeMetric.walkWeight G lp.physical (paths i).val : ℚ) : ℝ) ≤
          500000 * ((r : ℝ) * Statements.gridLevels h ratio) * lp.rentalBudget := by
  obtain ⟨output, _, buying, _, _, routes⟩ :=
    rounding_correct numbering lp lp.fractionalLength (fun _ => rfl) ratio r ratio_ge r_ge
  choose paths _ supported bounded using routes
  refine ⟨output.bought, buying, paths, supported, ?_⟩
  have bound : (∑ i, lp.demand i * NodeMetric.walkWeight G lp.physical (paths i).val : ℚ) ≤
      (500000 * r * gridDepth h ratio : ℚ) * lp.rentalBudget := by
    calc
      _ ≤ ∑ i, lp.demand i * ((500000 * r * gridDepth h ratio : ℚ) * lp.fractionalLength i) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (bounded i) (lp.demand_pos i).le
      _ = _ := by simp only [NodeLP.rentalBudget, Finset.mul_sum]; congr 1; funext i; ring
  have real_bound : ((∑ i, lp.demand i * NodeMetric.walkWeight G lp.physical (paths i).val : ℚ) : ℝ) ≤
      ((500000 * r * gridDepth h ratio : ℚ) : ℝ) * lp.rentalBudget := by exact_mod_cast bound
  simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat, gridDepth_eq_gridLevels, mul_assoc] using real_bound

end BuyAtBulk.Computation.Rounding
