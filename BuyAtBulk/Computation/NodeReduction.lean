import BuyAtBulk.Model.NodeReduction.EndpointProjection
import BuyAtBulk.Computation.FlowDecomposition.Search
import Mathlib.Data.List.NodupEquivFin

/-! Explicit materialized numbering of the subdivision graph from a supplied
numbering of the original graph. Pair labels include isolated nonedges, exactly
as in the mathematical reduction. No classical enumeration is evaluated. -/
namespace BuyAtBulk.Computation.NodeReduction
open BuyAtBulk.NodeReduction
variable (D : GraphData)

def vertexEncoding : Vertex D ≃ D.Vertex ⊕ (Sym2 D.Vertex ⊕ (Fin D.requestCount × Bool)) where
  toFun
    | .original v => .inl v
    | .edge e => .inr (.inl e)
    | .leaf i side => .inr (.inr (i, side))
  invFun
    | .inl v => .original v
    | .inr (.inl e) => .edge e
    | .inr (.inr (i, side)) => .leaf i side
  left_inv v := by cases v <;> rfl
  right_inv v := by rcases v with v | e | ⟨i, side⟩ <;> rfl

scoped instance vertexDecidableEq [DecidableEq D.Vertex] : DecidableEq (Vertex D) := fun u v =>
  decidable_of_iff (vertexEncoding D u = vertexEncoding D v) (vertexEncoding D).injective.eq_iff

scoped instance graphDecidableAdj [DecidableEq D.Vertex] [DecidableRel D.graph.Adj] :
    DecidableRel (graph D).Adj := by
  intro u v
  cases u <;> cases v <;> dsimp [graph] <;> infer_instance

variable [DecidableEq D.Vertex] {n : ℕ} (originalNumbering : D.Vertex ≃ Fin n)

def rawVertices : List (Vertex D) :=
  let originals := FlowDecomposition.vertices originalNumbering
  originals.map Vertex.original ++
    originals.flatMap (fun u => originals.map fun v => Vertex.edge s(u, v)) ++
    (List.finRange D.requestCount).flatMap (fun i => [Vertex.leaf i false, Vertex.leaf i true])

def vertexList : List (Vertex D) := (rawVertices D originalNumbering).dedup

theorem rawVertices_complete (v : Vertex D) : v ∈ rawVertices D originalNumbering := by
  cases v with
  | original v => simp [rawVertices, FlowDecomposition.vertices_complete]
  | edge e =>
    obtain ⟨⟨u, v⟩, rfl⟩ := Sym2.mk_surjective e
    simp only [rawVertices, List.mem_append, List.mem_map, List.mem_flatMap, FlowDecomposition.vertices_complete, true_and]
    exact Or.inl (Or.inr ⟨u, v, rfl⟩)
  | leaf i side => cases side <;> simp [rawVertices]

theorem vertexList_nodup : (vertexList D originalNumbering).Nodup := List.nodup_dedup _

theorem vertexList_complete (v : Vertex D) : v ∈ vertexList D originalNumbering := by
  simpa [vertexList] using rawVertices_complete D originalNumbering v

/-- Both directions execute list lookup/position in the explicit deduplicated
vertex list. The finite type used for indices has this computed list length. -/
def numbering : Vertex D ≃ Fin (vertexList D originalNumbering).length :=
  (List.Nodup.getEquivOfForallMemList (vertexList D originalNumbering)
    (vertexList_nodup D originalNumbering) (vertexList_complete D originalNumbering)).symm

theorem rawVertices_length : (rawVertices D originalNumbering).length = n + n * n + 2 * D.requestCount := by
  simp [rawVertices, List.length_flatMap, FlowDecomposition.vertices_length, mul_comm, Nat.add_assoc]

theorem numbering_size : (vertexList D originalNumbering).length ≤ n + n * n + 2 * D.requestCount := by
  exact (List.Sublist.length_le (List.dedup_sublist _)).trans_eq (rawVertices_length D originalNumbering)

end BuyAtBulk.Computation.NodeReduction
