import BuyAtBulk.Computation.Runtime.RoundingCorrectness

namespace BuyAtBulk.Computation.Runtime.StoredRounding
open BuyAtBulk.UpperBound
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)


theorem optimized_correct (lp : NodeLP input.graph h) (buying physical opening : Vector ℚ n) (budget : ℚ)
    (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (source_eq : lp.source=fun i => source[i.val]) (target_eq : lp.target=fun i => target[i.val])
    (buying_eq : lp.buying=fun v => buying[v.val]) (physical_eq : lp.physical=fun v => physical[v.val])
    (opening_eq : lp.opening=fun v => opening[v.val]) (budget_eq : budget=lp.buyingBudget)
    (metadata : ∀ i : Fin h, lengths[i.val]=lp.fractionalLength i) :
    ∃ output : Output input source target,
      (optimized input buying physical opening budget source target lengths).value=some output ∧
      (nodeBuying (fun v => buying[v.val]) (StoredState.boughtSet output.bought) : ℝ) ≤
        500000*Statements.buyingFactor h (Optimization.scaleRatio h) (Optimization.r h)*budget ∧
      (Rounding.rentalCost (fun v => physical[v.val]) lp.demand output.routes : ℝ) ≤
        500000*((Optimization.r h : ℝ)*Statements.gridLevels h (Optimization.scaleRatio h))*lp.rentalBudget ∧
      (output.routes.map fun entry => entry.1).Perm (List.finRange h) ∧
      ∀ entry∈output.routes, entry.2.val.support.toFinset⊆StoredState.boughtSet output.bought ∧
        NodeMetric.walkWeight input.graph (fun v => physical[v.val]) entry.2.val ≤
          (500000*Optimization.r h*gridDepth h (Optimization.scaleRatio h) : ℚ)*lp.fractionalLength entry.1 := by
  have girth : 1≤Optimization.r h := by
    unfold Optimization.r
    have spec := (Optimization.q_spec h).1
    omega
  obtain ⟨output,returned,buyingBound,rentalBound,permutation,bounds⟩ :=
    run_correct input lp buying physical opening budget source target lengths (Optimization.scaleRatio h) (Optimization.r h)
      (Optimization.scaleRatio_lower h) girth source_eq target_eq buying_eq physical_eq opening_eq budget_eq metadata
  refine ⟨output,?_,buyingBound,rentalBound,permutation,bounds⟩
  simpa only[optimized,OptimizedParameters.compute_value] using returned

end BuyAtBulk.Computation.Runtime.StoredRounding
