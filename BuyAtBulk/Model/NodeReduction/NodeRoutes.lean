import BuyAtBulk.Model.NodeReduction.NodeLPBridge
import BuyAtBulk.UpperBound.BuyingCosts

noncomputable section
namespace BuyAtBulk.NodeReduction
open scoped BigOperators
local instance nodeRoutesDecEq (D : GraphData) : DecidableEq (Vertex D) := Classical.decEq _
local instance nodeRoutesDecRel (D : GraphData) : DecidableRel (graph D).Adj := Classical.decRel _

/-- Encode actual all-node routes in the complete transformed path LP. -/
def encodeRoutes (D : GraphData)
    (paths : ∀ i, (graph D).Path (.leaf i false) (.leaf i true)) :
    (reduced D).toInstance.IntegralRouting where
  path := fun i => (reduced D).encode i (paths i)
  allowed_path := fun i => (reduced D).allowed_encode i (paths i)

theorem encodeRoutes_resources (D : GraphData)
    (paths : ∀ i, (graph D).Path (.leaf i false) (.leaf i true)) (a : Fin D.resourceCount) :
    a ∈ (reduced D).toInstance.usedResources (encodeRoutes D paths) ↔
      ∃ i, resourceVertex D a ∈ (paths i).val.support := by
  constructor
  · intro ha
    obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp ha
    change a ∈ (reduced D).toInstance.uses ((reduced D).encode i (paths i)) at hai
    rw [GraphData.uses_encode] at hai
    exact ⟨i, (reduced_resource_mem D i (paths i) a).mp hai⟩
  · rintro ⟨i, hi⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    change a ∈ (reduced D).toInstance.uses ((reduced D).encode i (paths i))
    rw [GraphData.uses_encode]
    exact (reduced_resource_mem D i (paths i) a).mpr hi

theorem nodeCost_bought (D : GraphData) (cost : Fin D.resourceCount → ℚ) (bought : Finset (Vertex D)) :
    UpperBound.nodeBuying (nodeCost D cost) bought =
      ∑ a, if resourceVertex D a ∈ bought then cost a else 0 := by
  classical
  have hsum := nodeCost_budget D cost (fun v => if v ∈ bought then 1 else 0)
  simpa [UpperBound.nodeBuying, mul_ite] using hsum

/-- The incidence routing pays at most the node-buying price of any bought
set supporting its actual paths; unused bought nodes are harmless. -/
theorem encodeRoutes_buying_le (D : GraphData)
    (paths : ∀ i, (graph D).Path (.leaf i false) (.leaf i true)) (bought : Finset (Vertex D))
    (supported : ∀ i, (paths i).val.support.toFinset ⊆ bought) :
    (reduced D).toInstance.integralBuyingCost (encodeRoutes D paths) ≤
      UpperBound.nodeBuying (nodeCost D D.buying) bought := by
  classical
  have subset : (reduced D).toInstance.usedResources (encodeRoutes D paths) ⊆
      Finset.univ.filter (fun a => resourceVertex D a ∈ bought) := by
    intro a ha
    obtain ⟨i, hi⟩ := (encodeRoutes_resources D paths a).mp ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, supported i (by simpa using hi)⟩
  change (∑ a ∈ (reduced D).toInstance.usedResources (encodeRoutes D paths), D.buying a) ≤ _
  rw [nodeCost_bought]
  calc
    _ ≤ ∑ a ∈ Finset.univ.filter (fun a => resourceVertex D a ∈ bought), D.buying a :=
      Finset.sum_le_sum_of_subset_of_nonneg subset (fun a ha hnot => D.buying_nonneg a)
    _ = _ := Finset.sum_filter _ _

theorem encodeRoutes_rental (D : GraphData)
    (paths : ∀ i, (graph D).Path (.leaf i false) (.leaf i true)) :
    (reduced D).toInstance.integralRentalCost (encodeRoutes D paths) =
      ∑ i, D.demand i * NodeMetric.walkWeight (graph D) (nodeCost D D.length) (paths i).val := by
  apply Finset.sum_congr rfl
  intro i hi
  change D.demand i * (reduced D).toInstance.pathLength ((reduced D).encode i (paths i)) = _
  rw [nodeCost_pathLength]

end BuyAtBulk.NodeReduction
