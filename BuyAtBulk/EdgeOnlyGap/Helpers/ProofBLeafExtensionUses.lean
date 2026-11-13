import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBLeafExtensionEdges
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBLeafRestrictionMap
noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofB
attribute [local instance] Classical.propDecidable

/-- Original edges are disjoint from every private pendant. -/
theorem leafOldEdgeNePendant (D : BuyAtBulk.GraphData) (p : ℚ) (hp : 0 ≤ p)
    (e : Sym2 D.Vertex) (j : Fin D.requestCount) (b : Bool) :
    Sym2.map (Sum.inl : D.Vertex → (privateLeaves D p hp).Vertex) e ≠
      s(Sum.inr (j,b), Sum.inl (if b then D.source j else D.target j)) := by
  induction e using Sym2.inductionOn with
  | hf u v =>
    rw [Sym2.map_mk]
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h,_⟩ | ⟨_,h⟩ <;> cases h

def leafPendantResource (D : BuyAtBulk.GraphData) (p : ℚ) (hp : 0 ≤ p)
    (j : Fin D.requestCount) (b : Bool) : Fin (privateLeaves D p hp).resourceCount :=
  Fintype.equivFin (Fin D.resourceCount ⊕ (Fin D.requestCount × Bool)) (Sum.inr (j,b))

set_option backward.isDefEq.respectTransparency false in
theorem leafExtensionOldUses (D : BuyAtBulk.GraphData) (edge : EdgeOnlyInstance D)
    (p : ℚ) (hp : 0 ≤ p) (i : Fin D.requestCount)
    (P : D.graph.Path (D.source i) (D.target i)) (a : Fin D.resourceCount) :
    leafOldResource D p hp a ∈ (privateLeaves D p hp).pathResources
      ⟨i,leafPathExtension D p hp i P⟩ ↔ a ∈ D.pathResources ⟨i,P⟩ := by
  classical
  obtain ⟨e,he⟩ := edge.2.1 a
  have loc : (privateLeaves D p hp).location (leafOldResource D p hp a) =
      Sum.inr (e.map Sum.inl) := by
    change (match (Fintype.equivFin (Fin D.resourceCount ⊕ (Fin D.requestCount × Bool))).symm
      (Fintype.equivFin _ (Sum.inl a)) with
      | Sum.inl j => match D.location j with
        | Sum.inl v => Sum.inl (Sum.inl v)
        | Sum.inr e => Sum.inr (e.map Sum.inl)
      | Sum.inr (j,b) => Sum.inr s(Sum.inr (j,b), Sum.inl (if b then D.source j else D.target j))) = _
    simp only [Equiv.symm_apply_apply, he]
  simp only [BuyAtBulk.GraphData.pathResources, Finset.mem_filter, Finset.mem_univ,
    true_and, loc, he]
  rw [leafExtensionEdges]
  have hs := leafOldEdgeNePendant D p hp e i true
  have ht := leafOldEdgeNePendant D p hp e i false
  rw [Sym2.eq_swap] at ht
  simp only [Bool.true_eq, ↓reduceIte, Bool.false_eq_true] at hs ht
  simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.mem_map, List.not_mem_nil, or_false]
  constructor
  · rintro (h | h | h)
    · exact False.elim (hs h)
    · obtain ⟨e',he',hh⟩ := h
      exact (Sym2.map.injective Sum.inl_injective hh) ▸ he'
    · exact False.elim (ht h)
  · intro h
    exact Or.inr (Or.inl ⟨e,h,rfl⟩)

set_option backward.isDefEq.respectTransparency false in
theorem leafExtensionPendantUses (D : BuyAtBulk.GraphData)
    (p : ℚ) (hp : 0 ≤ p) (i : Fin D.requestCount)
    (P : D.graph.Path (D.source i) (D.target i)) (j : Fin D.requestCount) (b : Bool) :
    leafPendantResource D p hp j b ∈ (privateLeaves D p hp).pathResources
      ⟨i,leafPathExtension D p hp i P⟩ ↔ j = i := by
  classical
  have loc : (privateLeaves D p hp).location (leafPendantResource D p hp j b) =
      Sum.inr s(Sum.inr (j,b), Sum.inl (if b then D.source j else D.target j)) := by
    change (match (Fintype.equivFin (Fin D.resourceCount ⊕ (Fin D.requestCount × Bool))).symm
      (Fintype.equivFin _ (Sum.inr (j,b))) with
      | Sum.inl a => match D.location a with
        | Sum.inl v => Sum.inl (Sum.inl v)
        | Sum.inr e => Sum.inr (e.map Sum.inl)
      | Sum.inr (j,b) => Sum.inr s(Sum.inr (j,b), Sum.inl (if b then D.source j else D.target j))) = _
    simp only [Equiv.symm_apply_apply]
  simp only [BuyAtBulk.GraphData.pathResources, Finset.mem_filter, Finset.mem_univ,
    true_and, loc]
  rw [leafExtensionEdges]
  have hold : ¬ ∃ e ∈ P.val.edges,
      Sym2.map (Sum.inl : D.Vertex → (privateLeaves D p hp).Vertex) e =
        s(Sum.inr (j,b), Sum.inl (if b then D.source j else D.target j)) := by
    rintro ⟨e,_,he⟩; exact leafOldEdgeNePendant D p hp e j b he
  simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.mem_map, hold, false_or]
  cases b <;> simp [Sym2.eq_iff, eq_comm] <;> (intro h; cases h; rfl)
end BuyAtBulk.EdgeOnlyGap.ProofB
