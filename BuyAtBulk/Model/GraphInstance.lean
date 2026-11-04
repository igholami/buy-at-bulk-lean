import BuyAtBulk.Model.GraphRealization
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting

/-! The exact finite all-simple-path LP induced by graph input. This constructor
is mathematical, not a polynomial-time enumeration algorithm. -/
namespace BuyAtBulk

structure GraphData where
  Vertex : Type
  vertexFintype : Fintype Vertex
  graph : SimpleGraph Vertex
  resourceCount : ℕ
  requestCount : ℕ
  source : Fin requestCount → Vertex
  target : Fin requestCount → Vertex
  location : Fin resourceCount → Vertex ⊕ Sym2 Vertex
  location_injective : Function.Injective location
  location_valid : ∀ a, match location a with
    | Sum.inl _ => True
    | Sum.inr edge => edge ∈ graph.edgeSet
  buying : Fin resourceCount → ℚ
  length : Fin resourceCount → ℚ
  demand : Fin requestCount → ℚ
  buying_nonneg : ∀ a, 0 ≤ buying a
  length_nonneg : ∀ a, 0 ≤ length a
  demand_pos : ∀ i, 0 < demand i

attribute [instance] GraphData.vertexFintype

namespace GraphData

abbrev TaggedPath (D : GraphData) :=
  (i : Fin D.requestCount) × D.graph.Path (D.source i) (D.target i)

noncomputable instance taggedPathFintype (D : GraphData) : Fintype D.TaggedPath := by
  classical
  unfold TaggedPath
  infer_instance

noncomputable def decode (D : GraphData) :
    Fin (Fintype.card D.TaggedPath) ≃ D.TaggedPath := (Fintype.equivFin D.TaggedPath).symm

noncomputable def encode (D : GraphData) (i : Fin D.requestCount)
    (path : D.graph.Path (D.source i) (D.target i)) : Fin (Fintype.card D.TaggedPath) :=
  D.decode.symm ⟨i, path⟩

@[simp] theorem decode_encode (D : GraphData) (i : Fin D.requestCount)
    (path : D.graph.Path (D.source i) (D.target i)) :
    D.decode (D.encode i path) = ⟨i, path⟩ := D.decode.apply_symm_apply _

noncomputable def pathResources (D : GraphData) (p : D.TaggedPath) :
    Finset (Fin D.resourceCount) := by
  classical
  exact Finset.univ.filter fun a => match D.location a with
    | Sum.inl v => v ∈ p.2.val.support
    | Sum.inr e => e ∈ p.2.val.edges

noncomputable abbrev toInstance (D : GraphData) : Instance := by
  classical
  exact {
    resourceCount := D.resourceCount
    requestCount := D.requestCount
    pathCount := Fintype.card D.TaggedPath
    allowed := fun i p => decide ((D.decode p).1 = i)
    uses := fun p => D.pathResources (D.decode p)
    buying := D.buying
    length := D.length
    demand := D.demand
    buying_nonneg := D.buying_nonneg
    length_nonneg := D.length_nonneg
    demand_pos := D.demand_pos }

@[simp] theorem allowed_encode (D : GraphData) (i : Fin D.requestCount)
    (path : D.graph.Path (D.source i) (D.target i)) :
    D.toInstance.allowed i (D.encode i path) = true := by
  classical
  simp

@[simp] theorem uses_encode (D : GraphData) (i : Fin D.requestCount)
    (path : D.graph.Path (D.source i) (D.target i)) :
    D.toInstance.uses (D.encode i path) = D.pathResources ⟨i, path⟩ := by
  classical
  simp [toInstance]

noncomputable def realization (D : GraphData) : D.toInstance.GraphRealization where
  Vertex := D.Vertex
  vertexFintype := D.vertexFintype
  graph := D.graph
  source := D.source
  target := D.target
  location := D.location
  location_injective := D.location_injective
  location_valid := D.location_valid
  path_sound := by
    classical
    intro i p hp
    have hi : (D.decode p).1 = i := by simpa [toInstance] using hp
    generalize hq : D.decode p = q at hi ⊢
    obtain ⟨j, path⟩ := q
    dsimp at hi
    subst j
    refine ⟨path.val, path.property.support_nodup, ?_⟩
    change D.pathResources (D.decode p) = _
    rw [hq]
    ext a
    simp only [pathResources, Instance.walkResources, Finset.mem_filter, Finset.mem_univ, true_and]
    cases ha : D.location a <;> simp_all
  path_complete := by
    classical
    intro i walk simple
    let path : D.graph.Path (D.source i) (D.target i) := ⟨walk, .mk' simple⟩
    refine ⟨D.encode i path, D.allowed_encode i path, ?_⟩
    erw [D.uses_encode]
    ext a
    simp only [pathResources, Instance.walkResources, Finset.mem_filter, Finset.mem_univ, true_and]
    cases ha : D.location a <;> simp_all [path]

end GraphData
end BuyAtBulk
