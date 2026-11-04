import BuyAtBulk.Model.NodeReduction.Construction
import BuyAtBulk.UpperBound.NodeLP

noncomputable section
namespace BuyAtBulk.NodeReduction
open scoped BigOperators
local instance nodeLPCostsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Push each old price or physical length onto its corresponding new node. -/
def nodeCost (D : GraphData) (cost : Fin D.resourceCount → ℚ) (v : Vertex D) : ℚ :=
  ∑ a, if resourceVertex D a = v then cost a else 0

/-- Assigned vertices retain the old opening, while every omitted/free node
(in particular every terminal leaf) is explicitly opened to one. -/
def nodeOpening (D : GraphData) (f : (reduced D).toInstance.FractionalSolution)
    (v : Vertex D) : ℚ :=
  if hv : ∃ a, resourceVertex D a = v then f.opening (Classical.choose hv) else 1

@[simp] theorem nodeOpening_resource (D : GraphData)
    (f : (reduced D).toInstance.FractionalSolution) (a : Fin D.resourceCount) :
    nodeOpening D f (resourceVertex D a) = f.opening a := by
  unfold nodeOpening
  split_ifs with hv
  · have ha := resourceVertex_injective D (Classical.choose_spec hv)
    rw [ha]
  · exact (hv ⟨a, rfl⟩).elim

theorem nodeOpening_bounds (D : GraphData) (f : (reduced D).toInstance.FractionalSolution)
    (hf : (reduced D).toInstance.Feasible f) (v : Vertex D) :
    0 ≤ nodeOpening D f v ∧ nodeOpening D f v ≤ 1 := by
  unfold nodeOpening
  split_ifs with hv
  · exact hf.1 _
  · norm_num

theorem nodeCost_nonneg (D : GraphData) (cost : Fin D.resourceCount → ℚ)
    (hc : ∀ a, 0 ≤ cost a) (v : Vertex D) : 0 ≤ nodeCost D cost v := by
  apply Finset.sum_nonneg
  intro a ha
  split_ifs
  · exact hc a
  · exact le_rfl

@[simp] theorem nodeCost_leaf (D : GraphData) (cost : Fin D.resourceCount → ℚ)
    (i : Fin D.requestCount) (side : Bool) : nodeCost D cost (.leaf i side) = 0 := by
  simp [nodeCost]

/-- Summation over all new vertices preserves a budget supported on paid
resources; this includes all free nodes with their explicit opening one. -/
theorem nodeCost_budget (D : GraphData) (cost : Fin D.resourceCount → ℚ)
    (opening : Vertex D → ℚ) :
    (∑ v, nodeCost D cost v * opening v) = ∑ a, cost a * opening (resourceVertex D a) := by
  classical
  unfold nodeCost
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  simp

/-- Node physical walk weight is exactly the sum of old resource lengths
whose corresponding subdivision vertices occur on that walk. -/
theorem nodeCost_walk (D : GraphData) (cost : Fin D.resourceCount → ℚ)
    {u v : Vertex D} (walk : (graph D).Walk u v) :
    NodeMetric.walkWeight (graph D) (nodeCost D cost) walk =
      ∑ a, if resourceVertex D a ∈ walk.support then cost a else 0 := by
  classical
  unfold NodeMetric.walkWeight nodeCost
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  simp

@[simp] theorem reduced_resource_mem (D : GraphData) (i : Fin D.requestCount)
    (path : (graph D).Path (.leaf i false) (.leaf i true)) (a : Fin D.resourceCount) :
    a ∈ (reduced D).pathResources ⟨i, path⟩ ↔ resourceVertex D a ∈ path.val.support := by
  classical
  simp [GraphData.pathResources, reduced]

theorem nodeCost_pathLength (D : GraphData) (i : Fin D.requestCount)
    (path : (graph D).Path (.leaf i false) (.leaf i true)) :
    NodeMetric.walkWeight (graph D) (nodeCost D D.length) path.val =
      (reduced D).toInstance.pathLength ((reduced D).encode i path) := by
  classical
  rw [nodeCost_walk]
  unfold Instance.pathLength
  rw [GraphData.uses_encode]
  change (∑ a, if resourceVertex D a ∈ path.val.support then D.length a else 0) =
    ∑ a ∈ (reduced D).pathResources ⟨i, path⟩, D.length a
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (reduced_resource_mem D i path a).symm
  · intro a ha
    rfl

end BuyAtBulk.NodeReduction
