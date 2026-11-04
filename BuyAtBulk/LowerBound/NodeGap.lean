import BuyAtBulk.LowerBound.UniformFeasibility
import BuyAtBulk.LowerBound.IntegralBridge
import BuyAtBulk.LowerBound.FractionalBridge
import BuyAtBulk.LowerBound.LogarithmicRatio
import BuyAtBulk.TheoremStatements

namespace BuyAtBulk.LowerBound

/-- Proposition `thm:node-lower`: for every `h ≥ 2`, an actual finite graph
with exactly `h` commodities, only node buying prices, zero physical lengths,
and gap strictly greater than one quarter of the base-two logarithm of `h`.
The certificate uses a feasible natural LP solution of cost two and a lower
bound on every integral routing, so no LP optimum attainment is assumed. -/
theorem node_gap : BuyAtBulk.NodeGapTarget := by
  intro h hh
  obtain ⟨k, hk, hcount, hratio⟩ := exists_logarithmic_scale h hh
  obtain ⟨request, hsurj⟩ := exists_request_surjection k h hk hcount
  let D := graphData k h request
  let f := uniformSolution k h request
  refine ⟨D.toInstance, rfl, D.realization, ?_, ?_,
    integralRouting_nonempty k h hk request, f, uniform_feasible k h hk request, ?_, ?_⟩
  · intro a
    exact ⟨Vertex.paid a, rfl⟩
  · intro a
    rfl
  · have hlower := graph_fractional_buying_lower k h hk request hsurj f
      (uniform_feasible k h hk request)
    linarith
  · intro routing
    have hlower := integralBuyingCost_lower k h hk request hsurj routing
    have hlowerReal : (k : ℝ) + 1 ≤ (D.toInstance.integralBuyingCost routing : ℝ) := by
      exact_mod_cast hlower
    have hcost : D.toInstance.buyingCost f = 2 := uniform_buyingCost k h hk request
    rw [hcost]
    norm_num only [Rat.cast_ofNat]
    rw [Real.logb] at hratio
    nlinarith

end BuyAtBulk.LowerBound
