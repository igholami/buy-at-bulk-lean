import BuyAtBulk.EdgeOnlyGap.Items.WitnessPaths

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 3: open all edges to 1/q, split on exactly the q displayed paths. -/
def fractionalWitness (H : FiniteGraph) (q d : ℕ) (π : Lift H q) (hd : 0 < d) :
    (supplyData H q d π hd).toInstance.FractionalSolution := by
  classical
  let D := supplyData H q d π hd
  let req := (Fintype.equivFin (Edges H)).symm
  exact {
    opening := fun _ => 1 / (q : ℚ)
    flow := fun i p => ∑ j : Fin q,
      if p = D.encode i (witnessPath H q π (req i) j) then 1 / (q : ℚ) else 0 }

end BuyAtBulk.EdgeOnlyGap
