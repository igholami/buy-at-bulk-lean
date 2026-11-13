import BuyAtBulk.EdgeOnlyGap.Items.MatchingTerminals

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 5: two private degree-one leaves per request, pendant buying and length p. -/
def privateLeaves (D : BuyAtBulk.GraphData) (p : ℚ) (hp : 0 ≤ p) :
    BuyAtBulk.GraphData := by
  classical
  let V := D.Vertex ⊕ (Fin D.requestCount × Bool)
  let G : SimpleGraph V := SimpleGraph.fromRel fun x y =>
    (∃ u v, x=Sum.inl u ∧ y=Sum.inl v ∧ D.graph.Adj u v) ∨
    (∃ i b, x=Sum.inr (i,b) ∧
      y=Sum.inl (if b then D.source i else D.target i))
  let R := Fin D.resourceCount ⊕ (Fin D.requestCount × Bool)
  let idx := (Fintype.equivFin R).symm
  exact {
    Vertex := V
    vertexFintype := inferInstance
    graph := G
    resourceCount := Fintype.card R
    requestCount := D.requestCount
    source := fun i => Sum.inr (i,true)
    target := fun i => Sum.inr (i,false)
    location := fun a => match idx a with
      | Sum.inl j => match D.location j with
        | Sum.inl v => Sum.inl (Sum.inl v)
        | Sum.inr e => Sum.inr (e.map Sum.inl)
      | Sum.inr (i,b) => Sum.inr (s(Sum.inr (i,b), Sum.inl (if b then D.source i else D.target i)))
    location_injective := by
      intro a b hab
      dsimp only at hab
      apply idx.injective
      generalize hxa : idx a = xa at hab
      generalize hxb : idx b = xb at hab
      have hdisjoint : ∀ (e : Sym2 D.Vertex) i b,
          e.map (Sum.inl : D.Vertex → V) ≠
            s(Sum.inr (i,b), Sum.inl (if b then D.source i else D.target i)) := by
        intro e i b h
        induction e using Sym2.inductionOn with
        | hf u w =>
          rw [Sym2.map_mk] at h
          rcases Sym2.eq_iff.mp h with ⟨h₁, _⟩ | ⟨_, h₂⟩
          · cases h₁
          · cases h₂
      rcases xa with ja | ⟨ia, ba⟩ <;> rcases xb with jb | ⟨ib, bb⟩
      · congr 1
        apply D.location_injective
        cases hla : D.location ja <;> cases hlb : D.location jb <;>
          simp only [hla, hlb, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at hab ⊢
        · exact Sum.inl.inj hab
        · exact Sym2.map.injective Sum.inl_injective hab
      · exfalso
        cases hla : D.location ja with
        | inl v => simp only [hla, reduceCtorEq] at hab
        | inr e =>
          simp only [hla, Sum.inr.injEq] at hab
          exact hdisjoint e ib bb hab
      · exfalso
        cases hlb : D.location jb with
        | inl v => simp only [hlb, reduceCtorEq] at hab
        | inr e =>
          simp only [hlb, Sum.inr.injEq] at hab
          exact hdisjoint e ia ba hab.symm
      · simp only [Sum.inr.injEq, Sym2.eq_iff] at hab
        rcases hab with ⟨h₁, _⟩ | ⟨h₁, _⟩
        · exact congrArg Sum.inr (Sum.inr.inj h₁)
        · cases h₁
    location_valid := by
      intro a
      rcases hxa : idx a with j | ⟨i, b⟩
      · have hv := D.location_valid j
        cases hlj : D.location j with
        | inl v => simpa only [hlj] using True.intro
        | inr e =>
          simp only [hlj]
          rw [hlj] at hv
          induction e using Sym2.inductionOn with
          | hf u w =>
            change G.Adj (Sum.inl u) (Sum.inl w)
            dsimp [G]
            have hadj : D.graph.Adj u w := hv
            rw [SimpleGraph.fromRel_adj]
            exact ⟨by intro h; exact hadj.ne (Sum.inl.inj h), Or.inl (Or.inl ⟨u, w, rfl, rfl, hadj⟩)⟩
      · change G.Adj (Sum.inr (i, b)) (Sum.inl (if b then D.source i else D.target i))
        dsimp [G]
        rw [SimpleGraph.fromRel_adj]
        exact ⟨by simp, Or.inl (Or.inr ⟨i, b, rfl, rfl⟩)⟩
    buying := fun a => match idx a with | Sum.inl j => D.buying j | Sum.inr _ => p
    length := fun a => match idx a with | Sum.inl j => D.length j | Sum.inr _ => p
    demand := D.demand
    buying_nonneg := by
      intro a
      rcases idx a with j | _
      · exact D.buying_nonneg j
      · exact hp
    length_nonneg := by
      intro a
      rcases idx a with j | _
      · exact D.length_nonneg j
      · exact hp
    demand_pos := D.demand_pos }

end BuyAtBulk.EdgeOnlyGap
