import BuyAtBulk.Model.NodeReduction.Compression

namespace BuyAtBulk.NodeReduction
open SimpleGraph

/-- Strip the two free endpoint leaves and compress the resulting simple path.
No transformed path is omitted: internal leaves are excluded by simplicity in
the compression theorem, and the distinct endpoints make both leaf edges real. -/
def projectWalk (D : GraphData) (i : Fin D.requestCount)
    (p : (graph D).Walk (.leaf i false) (.leaf i true)) (hp : p.IsPath) :
    { q : D.graph.Walk (D.source i) (D.target i) // q.IsPath ∧
      ∀ a : Fin D.resourceCount,
        (match D.location a with
        | Sum.inl vertex => vertex ∈ q.support
        | Sum.inr edge => edge ∈ q.edges) ↔ resourceVertex D a ∈ p.support } := by
  classical
  cases p with
  | @cons _ next _ hfirst tail =>
    have hnext : next = Vertex.original (D.source i) :=
      (leaf_neighbor_iff D i false next).mp hfirst
    subst next
    have hnonnil : ¬ tail.Nil := SimpleGraph.Walk.not_nil_of_ne (by intro h; cases h)
    have hlast : tail.penultimate = Vertex.original (D.target i) :=
      (leaf_neighbor_iff D i true tail.penultimate).mp (tail.adj_penultimate hnonnil).symm
    let interior := tail.dropLast.copy rfl hlast
    have hsimple : interior.IsPath := by
      apply SimpleGraph.Walk.IsPath.mk'
      simpa [interior] using hp.of_cons.dropLast.support_nodup
    have hspan := tail.support_dropLast_concat hnonnil
    have hmem : ∀ a : Fin D.resourceCount,
        resourceVertex D a ∈ interior.support ↔
          resourceVertex D a ∈ (SimpleGraph.Walk.cons hfirst tail).support := by
      intro a
      simp only [interior, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_cons]
      rw [← hspan]
      simp [resourceVertex_ne_leaf]
    let result := compressPath D interior hsimple
    let q := result.val
    have hq := result.property.1
    have hnodes := result.property.2.1
    have hedges := result.property.2.2
    refine ⟨q, hq, ?_⟩
    intro a
    cases ha : D.location a with
    | inl v =>
      have hmap := hmem a
      rw [resourceVertex_node D a v ha] at hmap
      rw [resourceVertex_node D a v ha]
      exact (hnodes v).trans hmap
    | inr e =>
      have hmap := hmem a
      rw [resourceVertex_edge D a e ha] at hmap
      rw [resourceVertex_edge D a e ha]
      exact (hedges e).trans hmap

/-- Existence follows from the actual leaf-stripping/compression program. -/
theorem exists_projected (D : GraphData) (i : Fin D.requestCount)
    (p : (graph D).Walk (.leaf i false) (.leaf i true)) (hp : p.IsPath) :
    ∃ q : D.graph.Walk (D.source i) (D.target i), q.IsPath ∧
      ∀ a : Fin D.resourceCount,
        (match D.location a with
        | Sum.inl vertex => vertex ∈ q.support
        | Sum.inr edge => edge ∈ q.edges) ↔ resourceVertex D a ∈ p.support :=
  ⟨(projectWalk D i p hp).val, (projectWalk D i p hp).property⟩

/-- Actual computational projection of a subdivision path to an original path. -/
def projectPath (D : GraphData) (i : Fin D.requestCount)
    (path : (graph D).Path (.leaf i false) (.leaf i true)) :
    D.graph.Path (D.source i) (D.target i) :=
  ⟨(projectWalk D i path.val path.property).val,
    (projectWalk D i path.val path.property).property.1⟩

/-- The projected output has at most one occurrence of every original
vertex, hence its path encoding has polynomial length. -/
theorem projectPath_length_lt (D : GraphData) (i : Fin D.requestCount)
    (path : (graph D).Path (.leaf i false) (.leaf i true)) :
    (projectPath D i path).val.length < Fintype.card D.Vertex :=
  (projectPath D i path).property.length_lt

/-- Every transformed simple path has exactly its original resource vector. -/
theorem projectPath_resources (D : GraphData) (i : Fin D.requestCount)
    (path : (graph D).Path (.leaf i false) (.leaf i true)) :
    D.pathResources ⟨i, projectPath D i path⟩ = (reduced D).pathResources ⟨i, path⟩ := by
  classical
  ext a
  simp only [GraphData.pathResources, Finset.mem_filter, Finset.mem_univ, true_and]
  have hmem := (projectWalk D i path.val path.property).property.2 a
  exact hmem

end BuyAtBulk.NodeReduction
