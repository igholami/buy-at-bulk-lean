import BuyAtBulk.Model.GraphInstance
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.NormNum

noncomputable section
namespace BuyAtBulk.NodeReduction

/-- Every edge is subdivided, and every request endpoint occurrence receives
its own new terminal leaf, even when original endpoints coincide. -/
inductive Vertex (D : GraphData) where
  | original (v : D.Vertex)
  | edge (e : Sym2 D.Vertex)
  | leaf (i : Fin D.requestCount) (target : Bool)
  deriving Fintype

def endpoint (D : GraphData) (i : Fin D.requestCount) (target : Bool) : D.Vertex :=
  if target then D.target i else D.source i

/-- The subdivision graph with endpoint-occurrence leaves. Vertices labeled
by nonedges are isolated and free; including them avoids dependent edge labels
and increases the vertex count by at most a quadratic factor. -/
def graph (D : GraphData) : SimpleGraph (Vertex D) where
  Adj u v := match u, v with
    | .original v, .edge e => e ∈ D.graph.edgeSet ∧ v ∈ e
    | .edge e, .original v => e ∈ D.graph.edgeSet ∧ v ∈ e
    | .original v, .leaf i side => v = endpoint D i side
    | .leaf i side, .original v => v = endpoint D i side
    | _, _ => False
  symm := ⟨by intro u v; cases u <;> cases v <;> simp_all⟩
  loopless := ⟨by intro u; cases u <;> simp⟩

/-- The old paid resource becomes a node, retaining its exact resource label. -/
def resourceVertex (D : GraphData) (a : Fin D.resourceCount) : Vertex D :=
  match D.location a with
  | Sum.inl v => .original v
  | Sum.inr e => .edge e

@[simp] theorem resourceVertex_node (D : GraphData) (a : Fin D.resourceCount)
    (v : D.Vertex) (h : D.location a = Sum.inl v) : resourceVertex D a = .original v := by
  simp [resourceVertex, h]

@[simp] theorem resourceVertex_edge (D : GraphData) (a : Fin D.resourceCount)
    (e : Sym2 D.Vertex) (h : D.location a = Sum.inr e) : resourceVertex D a = .edge e := by
  simp [resourceVertex, h]

theorem resourceVertex_injective (D : GraphData) : Function.Injective (resourceVertex D) := by
  intro a b hab
  apply D.location_injective
  cases ha : D.location a with
  | inl v =>
    cases hb : D.location b with
    | inl w =>
      have hvw : v = w := by simpa [resourceVertex, ha, hb] using hab
      simp [hvw]
    | inr e => simp [resourceVertex, ha, hb] at hab
  | inr e =>
    cases hb : D.location b with
    | inl w => simp [resourceVertex, ha, hb] at hab
    | inr f =>
      have heq : e = f := by
        simpa only [resourceVertex, ha, hb, Vertex.edge.injEq] using hab
      simp [heq]

@[simp] theorem resourceVertex_ne_leaf (D : GraphData) (a : Fin D.resourceCount)
    (i : Fin D.requestCount) (side : Bool) : resourceVertex D a ≠ .leaf i side := by
  cases h : D.location a <;> simp [resourceVertex, h]

/-- Exact node-only graph input. Resources omitted from this list, in
particular all new terminal leaves, have zero buying price and length. -/
noncomputable abbrev reduced (D : GraphData) : GraphData where
  Vertex := Vertex D
  vertexFintype := inferInstance
  graph := graph D
  resourceCount := D.resourceCount
  requestCount := D.requestCount
  source := fun i => .leaf i false
  target := fun i => .leaf i true
  location := fun a => Sum.inl (resourceVertex D a)
  location_injective := fun _ _ h => resourceVertex_injective D (Sum.inl.inj h)
  location_valid := fun _ => trivial
  buying := D.buying
  length := D.length
  demand := D.demand
  buying_nonneg := D.buying_nonneg
  length_nonneg := D.length_nonneg
  demand_pos := D.demand_pos

/-- Distinct endpoint occurrences remain distinct regardless of old endpoints. -/
theorem leaves_injective (D : GraphData) :
    Function.Injective (fun occurrence : Fin D.requestCount × Bool =>
      Vertex.leaf (D := D) occurrence.1 occurrence.2) := by
  rintro ⟨i, side⟩ ⟨j, side'⟩ h
  simpa only [Vertex.leaf.injEq, Prod.mk.injEq] using h

/-- Every endpoint occurrence has exactly its original endpoint as neighbor. -/
theorem leaf_neighbor_iff (D : GraphData) (i : Fin D.requestCount) (side : Bool)
    (v : Vertex D) : (graph D).Adj (.leaf i side) v ↔ v = .original (endpoint D i side) := by
  cases v <;> simp [graph]

end BuyAtBulk.NodeReduction
