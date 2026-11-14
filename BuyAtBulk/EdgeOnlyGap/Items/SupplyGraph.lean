import Mathlib.Combinatorics.SimpleGraph.Maps
import BuyAtBulk.EdgeOnlyGap.Items.LiftAsFiniteGraph

import BuyAtBulk.EdgeOnlyGap.Items.SupplyVertex

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 3: undirected simple supply adjacency. -/
def supplyGraph (H : FiniteGraph) (q : ℕ) (π : Lift H q) :
    SimpleGraph (SupplyVertex H q) :=
  SimpleGraph.fromRel fun x y =>
    (∃ v j, x = Sum.inl v ∧ y = Sum.inr (v,j)) ∨
    (∃ a b, x = Sum.inr a ∧ y = Sum.inr b ∧ (liftGraph H q π).Adj a b)

end BuyAtBulk.EdgeOnlyGap
