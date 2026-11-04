import BuyAtBulk.Model.NaturalLP
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-! Graph semantics for the finite incidence model. This is a specification,
not the node-subdivision reduction. Completeness includes ALL simple paths,
so a restricted path family cannot silently change the LP. -/
namespace BuyAtBulk.Instance

/-- The resource occurrences of a walk, including both endpoint nodes. -/
noncomputable def walkResources {V : Type} {G : SimpleGraph V} {u v : V}
    (I : BuyAtBulk.Instance)
    (location : Fin I.resourceCount → V ⊕ Sym2 V)
    (walk : G.Walk u v) : Finset (Fin I.resourceCount) := by
  classical
  exact Finset.univ.filter fun a => match location a with
    | Sum.inl vertex => vertex ∈ walk.support
    | Sum.inr edge => edge ∈ walk.edges

/-- Exact realization as a finite undirected graph with node/edge resources.
Unassigned nodes and edges carry zero costs, as in the paper. -/
structure GraphRealization (I : BuyAtBulk.Instance) where
  Vertex : Type
  vertexFintype : Fintype Vertex
  graph : SimpleGraph Vertex
  source : Fin I.requestCount → Vertex
  target : Fin I.requestCount → Vertex
  location : Fin I.resourceCount → Vertex ⊕ Sym2 Vertex
  location_injective : Function.Injective location
  location_valid : ∀ a, match location a with
    | Sum.inl _ => True
    | Sum.inr edge => edge ∈ graph.edgeSet
  path_sound : ∀ i p, I.allowed i p = true →
    ∃ walk : graph.Walk (source i) (target i),
      walk.support.Nodup ∧ I.uses p = I.walkResources location walk
  path_complete : ∀ i (walk : graph.Walk (source i) (target i)),
    walk.support.Nodup → ∃ p, I.allowed i p = true ∧
      I.uses p = I.walkResources location walk

end BuyAtBulk.Instance
