import BuyAtBulk.Computation.OriginalPipeline.Input
import BuyAtBulk.Model.NodeReduction.EndpointProjection
import BuyAtBulk.Model.NodeReduction.NodeRoutes
import BuyAtBulk.Computation.Rounding

/-! Structural original-path projection and exact original-resource output accounting. -/
set_option maxHeartbeats 1800000
namespace BuyAtBulk.Computation.OriginalPipeline
open BuyAtBulk.NodeReduction BuyAtBulk.CompactFlow
open scoped BuyAtBulk.Computation.NodeReduction
variable (D : GraphData) [DecidableEq D.Vertex] [DecidableRel D.graph.Adj]

structure OriginalOutput where
  bought : Finset (Fin D.resourceCount)
  routes : List D.TaggedPath

abbrev ReducedOutput := Rounding.Output (graph D)
  (fun i : Fin D.requestCount => Vertex.leaf i false) (fun i => Vertex.leaf i true)

def projectOutput (output : ReducedOutput D) : OriginalOutput D where
  bought := Finset.univ.filter (fun a => resourceVertex D a ∈ output.bought)
  routes := output.routes.map fun entry => ⟨entry.1, projectPath D entry.1 entry.2⟩

def outputBuying (output : OriginalOutput D) : ℚ := ∑ a ∈ output.bought, D.buying a

def outputRental (output : OriginalOutput D) : ℚ :=
  (output.routes.map fun entry => D.demand entry.1 * pathResourceCost D D.length entry.1 entry.2).sum

theorem projectOutput_buying (output : ReducedOutput D) :
    outputBuying D (projectOutput D output) =
      UpperBound.nodeBuying (resourceCost D D.buying) output.bought := by
  classical
  rw [show resourceCost D D.buying = nodeCost D D.buying from funext (resourceCost_eq D D.buying)]
  calc
    outputBuying D (projectOutput D output) =
        ∑ a, if resourceVertex D a ∈ output.bought then D.buying a else 0 := by
      simp [outputBuying, projectOutput, Finset.sum_filter]
    _ = UpperBound.nodeBuying (nodeCost D D.buying) output.bought := by
      convert (nodeCost_bought D D.buying output.bought).symm using 1
      · apply Finset.sum_congr rfl
        intro a _
        split_ifs <;> simp_all
      · unfold UpperBound.nodeBuying
        apply Finset.sum_congr (univ_independent _ _)
        intro v _
        split_ifs <;> simp_all

theorem projected_resource_iff (i : Fin D.requestCount)
    (path : (graph D).Path (.leaf i false) (.leaf i true)) (a : Fin D.resourceCount) :
    usesResource D i (projectPath D i path) a = true ↔ resourceVertex D a ∈ path.val.support := by
  have exact_mem := (projectWalk D i path.val path.property).property.2 a
  cases location : D.location a <;> simp only [usesResource, location] <;>
    exact decide_eq_true_iff.trans (by simpa only [projectPath, location] using exact_mem)

theorem projected_resourceCost (cost : Fin D.resourceCount → ℚ) (i : Fin D.requestCount)
    (path : (graph D).Path (.leaf i false) (.leaf i true)) :
    pathResourceCost D cost i (projectPath D i path) =
      NodeMetric.walkWeight (graph D) (resourceCost D cost) path.val := by
  classical
  rw [show resourceCost D cost = nodeCost D cost from funext (resourceCost_eq D cost), nodeCost_walk]
  unfold pathResourceCost
  apply Finset.sum_congr rfl
  intro a _
  simp only [projected_resource_iff]
  split_ifs <;> simp_all

theorem projectOutput_rental (output : ReducedOutput D) :
    outputRental D (projectOutput D output) =
      Rounding.rentalCost (resourceCost D D.length) D.demand output.routes := by
  rw [Rounding.rentalCost_eq]
  simp only [outputRental, projectOutput, List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro entry _
  rw [projected_resourceCost]

theorem projectOutput_indices (output : ReducedOutput D) :
    ((projectOutput D output).routes.map fun entry => entry.1) =
      output.routes.map fun entry => entry.1 := by
  simp [projectOutput, List.map_map]

theorem projectOutput_supported (output : ReducedOutput D)
    (supported : ∀ entry ∈ output.routes, entry.2.val.support.toFinset ⊆ output.bought) :
    ∀ entry ∈ (projectOutput D output).routes, ∀ a,
      usesResource D entry.1 entry.2 a = true → a ∈ (projectOutput D output).bought := by
  intro entry member a used
  obtain ⟨⟨i, path⟩, old_member, rfl⟩ := List.mem_map.mp member
  have old_used := (projected_resource_iff D i path a).mp used
  have bought := supported ⟨i, path⟩ old_member (by simpa using old_used)
  simpa [projectOutput] using bought

end BuyAtBulk.Computation.OriginalPipeline
