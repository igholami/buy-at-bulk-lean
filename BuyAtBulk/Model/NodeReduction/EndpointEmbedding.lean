import BuyAtBulk.Model.NodeReduction.Embedding

namespace BuyAtBulk.NodeReduction
open SimpleGraph

/-- Extend a subdivided simple path to its two distinct occurrence leaves.
This includes an original nil path when the endpoints coincide. -/
def liftPath (D : GraphData) (i : Fin D.requestCount)
    (path : D.graph.Path (D.source i) (D.target i)) :
    (graph D).Path (.leaf i false) (.leaf i true) := by
  have hs : (graph D).Adj (.leaf i false) (.original (D.source i)) := rfl
  have ht : (graph D).Adj (.original (D.target i)) (.leaf i true) := rfl
  let middle := subdivide D path.val
  have hm : middle.IsPath := subdivide_isPath D path.val path.property
  have htfree : Vertex.leaf i true ∉ middle.support := subdivide_leaf_notMem D _ _ _
  have hsfree : Vertex.leaf i false ∉ (middle.concat ht).support := by
    simp [middle]
  exact ⟨.cons hs (middle.concat ht), (hm.concat htfree ht).cons hsfree⟩

/-- Two free leaf incidences are the only additional output overhead. -/
@[simp] theorem liftPath_length (D : GraphData) (i : Fin D.requestCount)
    (path : D.graph.Path (D.source i) (D.target i)) :
    (liftPath D i path).val.length = 2 * path.val.length + 2 := by
  simp only [liftPath]
  erw [Walk.length_cons, Walk.length_concat, subdivide_length]

/-- No resource incidence changes when adding the two free leaves. -/
theorem liftPath_resource_mem (D : GraphData) (i : Fin D.requestCount)
    (path : D.graph.Path (D.source i) (D.target i)) (a : Fin D.resourceCount) :
    resourceVertex D a ∈ (liftPath D i path).val.support ↔
      (match D.location a with
      | Sum.inl vertex => vertex ∈ path.val.support
      | Sum.inr edge => edge ∈ path.val.edges) := by
  simp only [liftPath]
  erw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_concat]
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, resourceVertex_ne_leaf,
    false_or, or_false]
  exact subdivide_resource_mem D path.val a

/-- The exact complete-path incidence vectors agree in the two graph models. -/
theorem liftPath_resources (D : GraphData) (i : Fin D.requestCount)
    (path : D.graph.Path (D.source i) (D.target i)) :
    (reduced D).pathResources ⟨i, liftPath D i path⟩ = D.pathResources ⟨i, path⟩ := by
  classical
  ext a
  simp only [GraphData.pathResources, Finset.mem_filter, Finset.mem_univ, true_and]
  change (resourceVertex D a ∈ (liftPath D i path).val.support) ↔ _
  exact liftPath_resource_mem D i path a

end BuyAtBulk.NodeReduction
