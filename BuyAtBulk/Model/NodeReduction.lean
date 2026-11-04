import BuyAtBulk.Model.NodeReduction.PathMaps
import BuyAtBulk.Model.NodeReduction.Transport

namespace BuyAtBulk.NodeReduction

/-- Mathematical content of source `lem:node-reduction`. The explicitly
constructed node-cost graph has the same requests and distinct free terminal
leaves. Both LP and integral solutions extend and project with exactly equal
buying and rental budgets. All simple paths in both graphs are included.

Free graph vertices are omitted from the paid-resource list, using the model's
zero-price/zero-length default. This is equivalent to listing them with opening
one. Polynomial running time is a separate algorithmic semantics obligation. -/
theorem node_reduction (D : GraphData) :
    (reduced D).requestCount = D.requestCount ∧
    (∀ a, ∃ v, (reduced D).location a = Sum.inl v) ∧
    Function.Injective (fun occurrence : Fin D.requestCount × Bool =>
      Vertex.leaf (D := D) occurrence.1 occurrence.2) ∧
    (∀ a i side, resourceVertex D a ≠ Vertex.leaf i side) ∧
    (∀ i side v, (graph D).Adj (.leaf i side) v ↔ v = .original (endpoint D i side)) ∧
    (∀ f : D.toInstance.FractionalSolution, D.toInstance.Feasible f →
      ∃ g : (reduced D).toInstance.FractionalSolution,
        (reduced D).toInstance.Feasible g ∧
        (reduced D).toInstance.buyingCost g = D.toInstance.buyingCost f ∧
        (reduced D).toInstance.rentalCost g = D.toInstance.rentalCost f) ∧
    (∀ g : (reduced D).toInstance.FractionalSolution, (reduced D).toInstance.Feasible g →
      ∃ f : D.toInstance.FractionalSolution, D.toInstance.Feasible f ∧
        D.toInstance.buyingCost f = (reduced D).toInstance.buyingCost g ∧
        D.toInstance.rentalCost f = (reduced D).toInstance.rentalCost g) ∧
    (∀ routing : D.toInstance.IntegralRouting,
      ∃ mapped : (reduced D).toInstance.IntegralRouting,
        (reduced D).toInstance.usedResources mapped = D.toInstance.usedResources routing ∧
        (reduced D).toInstance.integralBuyingCost mapped = D.toInstance.integralBuyingCost routing ∧
        (reduced D).toInstance.integralRentalCost mapped = D.toInstance.integralRentalCost routing) ∧
    (∀ routing : (reduced D).toInstance.IntegralRouting,
      ∃ mapped : D.toInstance.IntegralRouting,
        D.toInstance.usedResources mapped = (reduced D).toInstance.usedResources routing ∧
        D.toInstance.integralBuyingCost mapped = (reduced D).toInstance.integralBuyingCost routing ∧
        D.toInstance.integralRentalCost mapped = (reduced D).toInstance.integralRentalCost routing) := by
  let E := reduced D
  refine ⟨rfl, (fun a => ⟨resourceVertex D a, rfl⟩), leaves_injective D,
    resourceVertex_ne_leaf D, leaf_neighbor_iff D, ?_, ?_, ?_, ?_⟩
  · intro f hf
    let g : E.toInstance.FractionalSolution :=
      transportFractional D.toInstance E.toInstance.pathCount E.toInstance.allowed
        E.toInstance.uses (liftCode D) f
    refine ⟨g, ?_, ?_, ?_⟩
    · exact transport_feasible D.toInstance _ _ _ (liftCode D)
        (liftCode_allowed D) (liftCode_uses D) f hf
    · exact transport_buyingCost D.toInstance _ _ _ (liftCode D) f
    · exact transport_rentalCost D.toInstance _ _ _ (liftCode D) (liftCode_uses D) f
  · intro g hg
    let f : D.toInstance.FractionalSolution :=
      transportFractional E.toInstance D.toInstance.pathCount D.toInstance.allowed
        D.toInstance.uses (projectCode D) g
    refine ⟨f, ?_, ?_, ?_⟩
    · exact transport_feasible E.toInstance _ _ _ (projectCode D)
        (projectCode_allowed D) (projectCode_uses D) g hg
    · exact transport_buyingCost E.toInstance _ _ _ (projectCode D) g
    · exact transport_rentalCost E.toInstance _ _ _ (projectCode D) (projectCode_uses D) g
  · intro routing
    let mapped : E.toInstance.IntegralRouting :=
      transportIntegral D.toInstance E.toInstance.pathCount E.toInstance.allowed
        E.toInstance.uses (liftCode D) (liftCode_allowed D) routing
    refine ⟨mapped, ?_, ?_, ?_⟩
    · exact transport_usedResources D.toInstance _ _ _ (liftCode D)
        (liftCode_allowed D) (liftCode_uses D) routing
    · exact transport_integralBuyingCost D.toInstance _ _ _ (liftCode D)
        (liftCode_allowed D) (liftCode_uses D) routing
    · exact transport_integralRentalCost D.toInstance _ _ _ (liftCode D)
        (liftCode_allowed D) (liftCode_uses D) routing
  · intro routing
    let mapped : D.toInstance.IntegralRouting :=
      transportIntegral E.toInstance D.toInstance.pathCount D.toInstance.allowed
        D.toInstance.uses (projectCode D) (projectCode_allowed D) routing
    refine ⟨mapped, ?_, ?_, ?_⟩
    · exact transport_usedResources E.toInstance _ _ _ (projectCode D)
        (projectCode_allowed D) (projectCode_uses D) routing
    · exact transport_integralBuyingCost E.toInstance _ _ _ (projectCode D)
        (projectCode_allowed D) (projectCode_uses D) routing
    · exact transport_integralRentalCost E.toInstance _ _ _ (projectCode D)
        (projectCode_allowed D) (projectCode_uses D) routing

end BuyAtBulk.NodeReduction
