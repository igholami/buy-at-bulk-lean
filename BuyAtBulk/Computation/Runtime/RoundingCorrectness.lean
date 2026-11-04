import BuyAtBulk.Computation.Runtime.OptimizedRounding
import BuyAtBulk.Computation.Rounding

set_option maxHeartbeats 2000000
namespace BuyAtBulk.Computation.Runtime.StoredRounding
open BuyAtBulk.UpperBound
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

/-- Numeric correctness adapter. The LP is a proof certificate only: the
stored program reads precisely the supplied numerical arrays and metadata. -/
theorem run_correct (lp : NodeLP input.graph h) (buying physical opening : Vector ℚ n) (budget : ℚ)
    (source target : Vector (Fin n) h) (lengths : Vector ℚ h) (ratio r : ℕ) (ratio_ge : 8≤ratio) (r_ge : 1≤r)
    (source_eq : lp.source=fun i => source[i.val]) (target_eq : lp.target=fun i => target[i.val])
    (buying_eq : lp.buying=fun v => buying[v.val]) (physical_eq : lp.physical=fun v => physical[v.val])
    (opening_eq : lp.opening=fun v => opening[v.val]) (budget_eq : budget=lp.buyingBudget)
    (metadata : ∀ i : Fin h, lengths[i.val]=lp.fractionalLength i) :
    ∃ output : Output input source target,
      (run input buying physical opening budget source target lengths ratio r (by omega)).value=some output ∧
      (nodeBuying (fun v => buying[v.val]) (StoredState.boughtSet output.bought) : ℝ) ≤
        500000*Statements.buyingFactor h ratio r*budget ∧
      (Rounding.rentalCost (fun v => physical[v.val]) lp.demand output.routes : ℝ) ≤
        500000*((r : ℝ)*Statements.gridLevels h ratio)*lp.rentalBudget ∧
      (output.routes.map fun entry => entry.1).Perm (List.finRange h) ∧
      ∀ entry∈output.routes, entry.2.val.support.toFinset⊆StoredState.boughtSet output.bought ∧
        NodeMetric.walkWeight input.graph (fun v => physical[v.val]) entry.2.val ≤
          (500000*r*gridDepth h ratio : ℚ)*lp.fractionalLength entry.1 := by
  cases lp with
  | mk src tgt buy phy demand op flow bn pn dp ob fn unit cap sb sp tb tp =>
    dsimp only at source_eq target_eq buying_eq physical_eq opening_eq
    subst src
    subst tgt
    subst buy
    subst phy
    subst op
    let model : NodeLP input.graph h :=
      ⟨(fun i => source[i.val]),(fun i => target[i.val]),(fun v => buying[v.val]),(fun v => physical[v.val]),demand,
        (fun v => opening[v.val]),flow,bn,pn,dp,ob,fn,unit,cap,sb,sp,tb,tp⟩
    obtain ⟨output,computed,buyBound,rentalBound,permutation,bounds⟩ :=
      Rounding.run_correct (Equiv.refl _) model (fun i => lengths[i.val]) metadata ratio r ratio_ge r_ge
    rw[←budget_eq] at computed buyBound
    have native := run_value input buying physical opening budget source target lengths ratio r (by omega)
    have mapped : (run input buying physical opening budget source target lengths ratio r (by omega)).value.map
        (decodeOutput input source target)=some output := native.trans computed
    obtain ⟨stored,returned,same⟩ := Option.map_eq_some_iff.mp mapped
    rw[←same] at buyBound rentalBound permutation bounds
    exact ⟨stored,returned,buyBound,rentalBound,permutation,bounds⟩

end BuyAtBulk.Computation.Runtime.StoredRounding
