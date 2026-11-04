import BuyAtBulk.Model.BoughtNetwork
import BuyAtBulk.Statements.OptimizedRounding

/-! The paper's bought-network conclusion, using actual shortest physical
paths in the purchased network rather than merely a chosen routing. -/
namespace BuyAtBulk.Statements

def GraphRoundedOutput (I : Instance) (realization : I.GraphRealization)
    (f : I.FractionalSolution) (buyingFactor rentalFactor : ℝ) : Prop :=
  ∃ network : I.BoughtNetwork realization,
    (network.buyingCost : ℝ) ≤ buyingFactor * I.buyingCost f ∧
    (network.rentalCost : ℝ) ≤ rentalFactor * I.rentalCost f

theorem graph_output_of_routes (I : Instance) (realization : I.GraphRealization)
    (f : I.FractionalSolution) (buyingFactor rentalFactor : ℝ)
    (rounded : ∃ routing : I.IntegralRouting,
      (I.integralBuyingCost routing : ℝ) ≤ buyingFactor * I.buyingCost f ∧
      (I.integralRentalCost routing : ℝ) ≤ rentalFactor * I.rentalCost f) :
    GraphRoundedOutput I realization f buyingFactor rentalFactor := by
  obtain ⟨routing, buying, rental⟩ := rounded
  refine ⟨routing.toBoughtNetwork I realization, ?_, ?_⟩
  · exact buying
  · have shorter : ((routing.toBoughtNetwork I realization).rentalCost : ℝ) ≤
        I.integralRentalCost routing := by exact_mod_cast routing.toBoughtNetwork_rental I realization
    exact shorter.trans rental

end BuyAtBulk.Statements
