import BuyAtBulk.Model.NodeReduction.NodeLPCosts
import BuyAtBulk.Model.NodeReduction.TypedFlows

noncomputable section
namespace BuyAtBulk.NodeReduction
open scoped BigOperators
local instance nodeLPBridgeDecEq (D : GraphData) : DecidableEq (Vertex D) := Classical.decEq _
local instance nodeLPBridgeDecRel (D : GraphData) : DecidableRel (graph D).Adj := Classical.decRel _

/-- The actual reduced graph LP as the typed all-node model used by the core
rounding algorithm. Every unassigned free node is explicitly opened to one. -/
def toNodeLP (D : GraphData) (f : (reduced D).toInstance.FractionalSolution)
    (hf : (reduced D).toInstance.Feasible f) :
    UpperBound.NodeLP (graph D) D.requestCount where
  source := fun i => .leaf i false
  target := fun i => .leaf i true
  buying := nodeCost D D.buying
  physical := nodeCost D D.length
  demand := D.demand
  opening := nodeOpening D f
  flow := fun i path => f.flow i ((reduced D).encode i path)
  buying_nonneg := nodeCost_nonneg D D.buying D.buying_nonneg
  physical_nonneg := nodeCost_nonneg D D.length D.length_nonneg
  demand_pos := D.demand_pos
  opening_bounds := nodeOpening_bounds D f hf
  flow_nonneg := fun i path => hf.2.1 i _
  unit := typed_flow_unit (reduced D) f hf
  capacity := by
    intro i v
    by_cases hv : ∃ a, resourceVertex D a = v
    · obtain ⟨a, rfl⟩ := hv
      rw [nodeOpening_resource]
      have hsum := typed_resourceFlow (reduced D) f hf i a
      calc
        _ = ∑ path : (graph D).Path (.leaf i false) (.leaf i true),
            if a ∈ (reduced D).pathResources ⟨i, path⟩ then
              f.flow i ((reduced D).encode i path) else 0 := by
          apply Finset.sum_congr rfl
          intro path hp
          have hm := reduced_resource_mem D i path a
          by_cases hv : resourceVertex D a ∈ path.val.support
          · have ha := hm.mpr hv
            simp only [ite_eq_left hv, ite_eq_left ha]
          · have ha : a ∉ (reduced D).pathResources ⟨i, path⟩ := fun ha => hv (hm.mp ha)
            simp only [ite_eq_right hv, ite_eq_right ha]
        _ ≤ f.opening a := hsum.trans_le (hf.2.2.2.2 i a)
    · have hopen : nodeOpening D f v = 1 := by simp [nodeOpening, hv]
      rw [hopen]
      calc
        _ ≤ ∑ path, f.flow i ((reduced D).encode i path) := by
          apply Finset.sum_le_sum
          intro path hp
          split_ifs
          · exact le_rfl
          · exact hf.2.1 i _
        _ = 1 := typed_flow_unit (reduced D) f hf i
  source_buying := fun i => nodeCost_leaf D D.buying i false
  source_physical := fun i => nodeCost_leaf D D.length i false
  target_buying := fun i => nodeCost_leaf D D.buying i true
  target_physical := fun i => nodeCost_leaf D D.length i true

/-- The typed model has exactly the original fractional buying budget. -/
theorem toNodeLP_buyingBudget (D : GraphData) (f : (reduced D).toInstance.FractionalSolution)
    (hf : (reduced D).toInstance.Feasible f) :
    (toNodeLP D f hf).buyingBudget = (reduced D).toInstance.buyingCost f := by
  change (∑ v, nodeCost D D.buying v * nodeOpening D f v) = _
  rw [nodeCost_budget]
  simp only [nodeOpening_resource]
  rfl

/-- The typed model has exactly the original fractional physical length for
each request, with all endpoint leaves contributing zero physical length. -/
theorem toNodeLP_fractionalLength (D : GraphData) (f : (reduced D).toInstance.FractionalSolution)
    (hf : (reduced D).toInstance.Feasible f) (i : Fin D.requestCount) :
    (toNodeLP D f hf).fractionalLength i = (reduced D).toInstance.fractionalLength f i := by
  change (∑ path : (graph D).Path (.leaf i false) (.leaf i true),
    NodeMetric.walkWeight (graph D) (nodeCost D D.length) path.val *
      f.flow i ((reduced D).encode i path)) = _
  simp_rw [nodeCost_pathLength]
  let E := reduced D
  have hsum := weighted_request_sum E f hf i
    (fun tagged => E.toInstance.pathLength (E.decode.symm tagged))
  simpa only [Equiv.symm_apply_apply, GraphData.encode, Instance.fractionalLength] using hsum.symm

/-- The typed all-node representation preserves the separate rental budget. -/
theorem toNodeLP_rentalBudget (D : GraphData) (f : (reduced D).toInstance.FractionalSolution)
    (hf : (reduced D).toInstance.Feasible f) :
    (toNodeLP D f hf).rentalBudget = (reduced D).toInstance.rentalCost f := by
  apply Finset.sum_congr rfl
  intro i hi
  change D.demand i * (toNodeLP D f hf).fractionalLength i = _
  rw [toNodeLP_fractionalLength]

end BuyAtBulk.NodeReduction
