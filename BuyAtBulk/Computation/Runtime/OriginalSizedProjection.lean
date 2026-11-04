import BuyAtBulk.Computation.Runtime.OriginalSizedInverse
import BuyAtBulk.Computation.Runtime.OriginalProjection

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.Computation.Runtime.Original
open BuyAtBulk.NodeReduction BuyAtBulk.Computation.StoredOriginal
open scoped BuyAtBulk.Computation.NodeReduction
variable {n resources requests : ℕ} (tables : Tables n resources requests)
section Projection
variable (vertices : List (Vertex tables.graphData)) (same : vertices=modelVertices tables)
  (m : ℕ) (size : m=vertices.length)

def projectSized (i : Fin requests)
    (path : (sizedGraph tables vertices m size).value.graph.Path
      (sizedNumbering tables vertices same m size (.leaf i false))
      (sizedNumbering tables vertices same m size (.leaf i true))) :
    Traced (tables.graphData.graph.Path (tables.graphData.source i) (tables.graphData.target i)) :=
  let decoded := inverseSizedPath tables vertices same m size path
  let reduced := ShortestPath.copyPath decoded.value
    ((sizedNumbering tables vertices same m size).symm_apply_apply (.leaf i false))
    ((sizedNumbering tables vertices same m size).symm_apply_apply (.leaf i true))
  let output := project tables i reduced
  ⟨output.value,decoded.events++output.events⟩

theorem projectSized_value (i : Fin requests)
    (path : (sizedGraph tables vertices m size).value.graph.Path
      (sizedNumbering tables vertices same m size (.leaf i false))
      (sizedNumbering tables vertices same m size (.leaf i true))) :
    (projectSized tables vertices same m size i path).value=projectPath tables.graphData i
      (ShortestPath.copyPath (path.map (sizedIso tables vertices same m size).symm.toHom (sizedIso tables vertices same m size).symm.injective)
        ((sizedNumbering tables vertices same m size).symm_apply_apply (.leaf i false))
        ((sizedNumbering tables vertices same m size).symm_apply_apply (.leaf i true))) := by
  simp only [projectSized,project_value,inverseSizedPath_value]

theorem inverseSizedPath_length {u v : Fin m} (path : (sizedGraph tables vertices m size).value.graph.Path u v) :
    (inverseSizedPath tables vertices same m size path).value.val.length=path.val.length := by
  rw [inverseSizedPath_value]
  exact SimpleGraph.Walk.length_map _ _

theorem projectSized_count (i : Fin requests)
    (path : (sizedGraph tables vertices m size).value.graph.Path
      (sizedNumbering tables vertices same m size (.leaf i false))
      (sizedNumbering tables vertices same m size (.leaf i true))) :
    (projectSized tables vertices same m size i path).events.length ≤ (14*(m+1)+17)*(path.val.length+1)+10 := by
  have inverse := inverseSizedWalk_count tables vertices same m size path.val
  have projection := project_count tables i (ShortestPath.copyPath (inverseSizedPath tables vertices same m size path).value
    ((sizedNumbering tables vertices same m size).symm_apply_apply (.leaf i false))
    ((sizedNumbering tables vertices same m size).symm_apply_apply (.leaf i true)))
  simp only [ShortestPath.copyPath,SimpleGraph.Walk.length_copy,inverseSizedPath_length] at projection
  simp only [projectSized,List.length_append]
  change (inverseSizedWalk tables vertices same m size path.val).events.length+_ ≤ _
  dsimp only [ShortestPath.copyPath]
  nlinarith

theorem projectSized_words (i : Fin requests)
    (path : (sizedGraph tables vertices m size).value.graph.Path
      (sizedNumbering tables vertices same m size (.leaf i false))
      (sizedNumbering tables vertices same m size (.leaf i true)))
    (K : ℕ) (dimension : n+requests+m+6 ≤ K) :
    WordsWithin K (projectSized tables vertices same m size i path).events := by
  have inverse := inverseSizedWalk_words tables vertices same m size path.val K (by omega)
  have length := path.property.length_lt
  simp only [Fintype.card_fin] at length
  have projection := project_words tables i (ShortestPath.copyPath (inverseSizedPath tables vertices same m size path).value
    ((sizedNumbering tables vertices same m size).symm_apply_apply (.leaf i false))
    ((sizedNumbering tables vertices same m size).symm_apply_apply (.leaf i true))) K (by
      simp only [ShortestPath.copyPath,SimpleGraph.Walk.length_copy,inverseSizedPath_length]
      omega)
  exact (wordsWithin_append K _ _).mpr ⟨inverse,projection⟩

theorem projectSized_resourceCost (i : Fin requests)
    (path : (sizedGraph tables vertices m size).value.graph.Path
      (sizedNumbering tables vertices same m size (.leaf i false))
      (sizedNumbering tables vertices same m size (.leaf i true))) (cost : Fin resources→ℚ) :
    OriginalPipeline.pathResourceCost tables.graphData cost i (projectSized tables vertices same m size i path).value=
      NodeMetric.walkWeight (sizedGraph tables vertices m size).value.graph
        (fun v=>OriginalPipeline.resourceCost tables.graphData cost ((sizedNumbering tables vertices same m size).symm v)) path.val := by
  rw [projectSized_value,OriginalPipeline.projected_resourceCost,ShortestPath.copyPath_weight]
  exact ShortestPath.map_walkWeight (sizedIso tables vertices same m size).symm _ path.val

theorem projectSized_resource_iff (i : Fin requests)
    (path : (sizedGraph tables vertices m size).value.graph.Path
      (sizedNumbering tables vertices same m size (.leaf i false))
      (sizedNumbering tables vertices same m size (.leaf i true))) (a : Fin resources) :
    OriginalPipeline.usesResource tables.graphData i (projectSized tables vertices same m size i path).value a=true ↔
      sizedNumbering tables vertices same m size (resourceVertex tables.graphData a)∈path.val.support := by
  rw [projectSized_value,OriginalPipeline.projected_resource_iff]
  simp only [ShortestPath.copyPath,SimpleGraph.Walk.support_copy,SimpleGraph.Path.map,SimpleGraph.Walk.support_map,List.mem_map]
  constructor
  · rintro ⟨v,member,equal⟩
    have actual : (sizedNumbering tables vertices same m size).symm v=resourceVertex tables.graphData a := equal
    have index := congrArg (sizedNumbering tables vertices same m size) actual
    have eq : v=sizedNumbering tables vertices same m size (resourceVertex tables.graphData a) := by simpa using index
    exact eq ▸ member
  · intro member
    exact ⟨sizedNumbering tables vertices same m size (resourceVertex tables.graphData a),member,
      (sizedNumbering tables vertices same m size).symm_apply_apply _⟩
end Projection
end BuyAtBulk.Computation.Runtime.Original
