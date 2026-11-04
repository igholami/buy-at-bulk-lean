import BuyAtBulk.LowerBound.GraphLP

namespace BuyAtBulk.LowerBound
open scoped BigOperators

/-- Direct two-edge paths provide an integral routing for every occurrence. -/
theorem integralRouting_nonempty (k h : ℕ) (hk : 1 ≤ k)
    (request : Fin h → Request k) :
    Nonempty (graphData k h request).toInstance.IntegralRouting := by
  classical
  let D := graphData k h request
  have hpaths : ∀ i : Fin h, ∃ p, D.toInstance.allowed i p = true := by
    intro i
    have hc : 0 < (request i).val.card := by rw [(request i).property]; omega
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hc
    exact ⟨D.encode i (shortPath k (request i) ⟨j, hj⟩), D.allowed_encode _ _⟩
  choose p hp using hpaths
  exact ⟨⟨p, hp⟩⟩

/-- Any routing in the complete graph-path LP buys a hitting set, even if its
paths visit other request terminals. -/
theorem routing_networkFeasible (k h : ℕ) (request : Fin h → Request k)
    (hsurj : Function.Surjective request)
    (routing : (graphData k h request).toInstance.IntegralRouting) :
    NetworkFeasible k ((graphData k h request).toInstance.usedResources routing) := by
  classical
  let D := graphData k h request
  apply (repeated_connectivity_iff k h request hsurj _).mp
  intro i
  obtain ⟨walk, simple, huses⟩ := D.realization.path_sound i (routing.path i) (routing.allowed_path i)
  refine ⟨walk, ?_⟩
  intro j hj
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rw [huses]
  change j ∈ Finset.univ.filter (fun a => Vertex.paid a ∈ walk.support)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩

/-- The paper's integral lower bound holds in the complete graph-path model. -/
theorem integralBuyingCost_lower (k h : ℕ) (hk : 1 ≤ k)
    (request : Fin h → Request k) (hsurj : Function.Surjective request)
    (routing : (graphData k h request).toInstance.IntegralRouting) :
    (k + 1 : ℚ) ≤ (graphData k h request).toInstance.integralBuyingCost routing := by
  have hcover := routing_networkFeasible k h request hsurj routing
  have hcard := (network_integral_optimum k hk).1 _ hcover
  have hcost : (graphData k h request).toInstance.integralBuyingCost routing =
      (((graphData k h request).toInstance.usedResources routing).card : ℚ) := by
    simp [Instance.integralBuyingCost, graphData, GraphData.toInstance]
  rw [hcost]
  exact_mod_cast hcard

/-- A bought hitting set routes every repeated request on a direct simple path. -/
theorem routing_of_cover (k h : ℕ) (request : Fin h → Request k)
    (C : Finset (Ground k)) (hC : HitsAll k C) :
    ∃ routing : (graphData k h request).toInstance.IntegralRouting,
      (graphData k h request).toInstance.usedResources routing ⊆ C := by
  classical
  let D := graphData k h request
  have hchoices : ∀ i : Fin h, ∃ j : (request i).val, j.val ∈ C := by
    intro i
    obtain ⟨j, hjA, hjC⟩ := hC (request i).val (request i).property
    exact ⟨⟨j, hjA⟩, hjC⟩
  choose j hj using hchoices
  let routing : D.toInstance.IntegralRouting :=
    ⟨fun i => D.encode i (shortPath k (request i) (j i)), fun i => D.allowed_encode _ _⟩
  refine ⟨routing, ?_⟩
  intro a ha
  obtain ⟨i, _, hai⟩ := Finset.mem_biUnion.mp ha
  have hae : a = (j i).val := by
    have hres : D.toInstance.uses (D.encode i (shortPath k (request i) (j i))) = {(j i).val} :=
      (D.uses_encode i _).trans (shortPath_resources k h request i (j i))
    change a ∈ D.toInstance.uses (D.encode i (shortPath k (request i) (j i))) at hai
    rw [hres] at hai
    exact Finset.mem_singleton.mp hai
  simpa [hae] using hj i

/-- The complete graph-path integral problem attains buying optimum `k+1`. -/
theorem integralBuyingCost_exact (k h : ℕ) (hk : 1 ≤ k)
    (request : Fin h → Request k) (hsurj : Function.Surjective request) :
    ∃ routing : (graphData k h request).toInstance.IntegralRouting,
      (graphData k h request).toInstance.integralBuyingCost routing = (k + 1 : ℚ) := by
  obtain ⟨_, C, hC, hcard⟩ := integral_optimum k hk
  obtain ⟨routing, hsub⟩ := routing_of_cover k h request C hC
  refine ⟨routing, le_antisymm ?_ (integralBuyingCost_lower k h hk request hsurj routing)⟩
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  have hcost : (graphData k h request).toInstance.integralBuyingCost routing =
      (((graphData k h request).toInstance.usedResources routing).card : ℚ) := by
    simp [Instance.integralBuyingCost, graphData, GraphData.toInstance]
  rw [hcost]
  exact_mod_cast hle

end BuyAtBulk.LowerBound
