import BuyAtBulk.Model.NodeReduction.Construction

namespace BuyAtBulk.NodeReduction
open SimpleGraph

/-- The explicit subdivision representation has polynomially many nodes,
even though it also contains free isolated labels for original nonedges. -/
theorem subdivision_vertex_bound (D : GraphData) :
    Fintype.card (Vertex D) ≤ Fintype.card D.Vertex +
      Fintype.card D.Vertex * Fintype.card D.Vertex + 2 * D.requestCount := by
  let encoding : Vertex D ≃ D.Vertex ⊕ (Sym2 D.Vertex ⊕ (Fin D.requestCount × Bool)) := {
    toFun := fun v => match v with
      | .original u => .inl u
      | .edge e => .inr (.inl e)
      | .leaf i side => .inr (.inr (i, side))
    invFun := fun v => match v with
      | .inl u => .original u
      | .inr (.inl e) => .edge e
      | .inr (.inr (i, side)) => .leaf i side
    left_inv := by intro v; cases v <;> rfl
    right_inv := by rintro (v | e | ⟨i, side⟩) <;> rfl }
  have symmetry : Fintype.card (Sym2 D.Vertex) ≤ Fintype.card D.Vertex * Fintype.card D.Vertex := by
    have surjection := Fintype.card_le_of_surjective (Sym2.mk (α := D.Vertex)).uncurry Sym2.mk_surjective
    simpa only [Fintype.card_prod] using surjection
  have cardinality := Fintype.card_congr encoding
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at cardinality
  omega

/-- Replace every original edge by its two subdivision incidences. -/
def subdivide (D : GraphData) {u v : D.Vertex} (p : D.graph.Walk u v) :
    (graph D).Walk (.original u) (.original v) := by
  match p with
  | .nil => exact .nil
  | @SimpleGraph.Walk.cons _ _ u w v h tail =>
    have he : s(u, w) ∈ D.graph.edgeSet := by simpa using h
    exact .cons (show (graph D).Adj (.original u) (.edge s(u, w)) from ⟨he, by simp⟩)
      (.cons (show (graph D).Adj (.edge s(u, w)) (.original w) from ⟨he, by simp⟩)
        (subdivide D tail))

/-- The computed subdivision emits exactly two incidences per old edge. -/
@[simp] theorem subdivide_length (D : GraphData) {u v : D.Vertex} (p : D.graph.Walk u v) :
    (subdivide D p).length = 2 * p.length := by
  induction p <;> simp_all [subdivide] <;> omega

@[simp] theorem subdivide_original_mem (D : GraphData) {u v : D.Vertex}
    (p : D.graph.Walk u v) (w : D.Vertex) :
    Vertex.original w ∈ (subdivide D p).support ↔ w ∈ p.support := by
  induction p <;> simp_all [subdivide]

@[simp] theorem subdivide_edge_mem (D : GraphData) {u v : D.Vertex}
    (p : D.graph.Walk u v) (e : Sym2 D.Vertex) :
    Vertex.edge e ∈ (subdivide D p).support ↔ e ∈ p.edges := by
  induction p <;> simp_all [subdivide]

@[simp] theorem subdivide_leaf_notMem (D : GraphData) {u v : D.Vertex}
    (p : D.graph.Walk u v) (i : Fin D.requestCount) (side : Bool) :
    Vertex.leaf i side ∉ (subdivide D p).support := by
  induction p <;> simp_all [subdivide]

/-- Subdivision preserves simplicity, using both vertex and edge distinctness
of an original simple path. -/
theorem subdivide_isPath (D : GraphData) {u v : D.Vertex}
    (p : D.graph.Walk u v) (hp : p.IsPath) : (subdivide D p).IsPath := by
  induction p with
  | nil => exact .nil
  | @cons u w v h p ih =>
    have hsub := ih hp.of_cons
    have hroot : u ∉ p.support := (SimpleGraph.Walk.cons_isPath_iff h p).mp hp |>.2
    have hedge : s(u, w) ∉ p.edges := (SimpleGraph.Walk.isTrail_cons h p).mp hp.isTrail |>.2
    have he : s(u, w) ∈ D.graph.edgeSet := by simpa using h
    have hinner : (graph D).Adj (.edge s(u, w)) (.original w) := ⟨he, by simp⟩
    have houter : (graph D).Adj (.original u) (.edge s(u, w)) := ⟨he, by simp⟩
    have hmid : Vertex.edge s(u, w) ∉ (subdivide D p).support := by simpa using hedge
    have hstart : Vertex.original u ∉ (SimpleGraph.Walk.cons hinner (subdivide D p)).support := by
      simpa using hroot
    exact (hsub.cons hmid).cons hstart

/-- Every old resource has exactly the same path incidence after subdivision. -/
theorem subdivide_resource_mem (D : GraphData) {u v : D.Vertex}
    (p : D.graph.Walk u v) (a : Fin D.resourceCount) :
    resourceVertex D a ∈ (subdivide D p).support ↔
      (match D.location a with
      | Sum.inl vertex => vertex ∈ p.support
      | Sum.inr edge => edge ∈ p.edges) := by
  cases ha : D.location a <;> simp [resourceVertex, ha]

end BuyAtBulk.NodeReduction
