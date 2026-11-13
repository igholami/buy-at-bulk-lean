import BuyAtBulk.EdgeOnlyGap.Items.PrivateLeaves

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofB

/-- Private pendant edges preserve full edge-resource coverage and unit demands. -/
theorem leafEdgeOnly (D : BuyAtBulk.GraphData) (edge : EdgeOnlyInstance D)
    (p : ℚ) (hp : 0 ≤ p) : EdgeOnlyInstance (privateLeaves D p hp) := by
  classical
  let idx := (Fintype.equivFin (Fin D.resourceCount ⊕ (Fin D.requestCount × Bool))).symm
  refine ⟨edge.1, ?_, ?_⟩
  · intro a
    change ∃ e, (match idx a with
      | Sum.inl j => match D.location j with
        | Sum.inl v => Sum.inl (Sum.inl v)
        | Sum.inr e => Sum.inr (e.map Sum.inl)
      | Sum.inr (i,b) => Sum.inr (s(Sum.inr (i,b), Sum.inl (if b then D.source i else D.target i)))) = Sum.inr e
    rcases idx a with j | ⟨i,b⟩
    · obtain ⟨e, he⟩ := edge.2.1 j
      simp only [he]
      exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · intro e he
    change Sym2 (D.Vertex ⊕ (Fin D.requestCount × Bool)) at e
    induction e using Sym2.inductionOn with
    | hf x y =>
      change (privateLeaves D p hp).graph.Adj x y at he
      change (SimpleGraph.fromRel _).Adj x y at he
      rw [SimpleGraph.fromRel_adj] at he
      have old : ∀ u v, D.graph.Adj u v →
          ∃ a, (privateLeaves D p hp).location a = Sum.inr (s(Sum.inl u, Sum.inl v)) := by
        intro u v huv
        obtain ⟨a, ha⟩ := edge.2.2 s(u,v) huv
        refine ⟨idx.symm (Sum.inl a), ?_⟩
        change (match idx (idx.symm (Sum.inl a)) with
          | Sum.inl j => match D.location j with
            | Sum.inl w => Sum.inl (Sum.inl w)
            | Sum.inr e => Sum.inr (e.map Sum.inl)
          | Sum.inr (i,b) => Sum.inr (s(Sum.inr (i,b), Sum.inl (if b then D.source i else D.target i)))) = _
        simp [ha] <;> rfl
      have pendant : ∀ i b, ∃ a, (privateLeaves D p hp).location a =
          Sum.inr (s(Sum.inr (i,b), Sum.inl (if b then D.source i else D.target i))) := by
        intro i b
        refine ⟨idx.symm (Sum.inr (i,b)), ?_⟩
        change (match idx (idx.symm (Sum.inr (i,b))) with
          | Sum.inl j => match D.location j with
            | Sum.inl w => Sum.inl (Sum.inl w)
            | Sum.inr e => Sum.inr (e.map Sum.inl)
          | Sum.inr (i,b) => Sum.inr (s(Sum.inr (i,b), Sum.inl (if b then D.source i else D.target i)))) = _
        simp <;> rfl
      rcases he.2 with (⟨u,v,rfl,rfl,huv⟩ | ⟨i,b,rfl,rfl⟩) |
        (⟨u,v,rfl,rfl,huv⟩ | ⟨i,b,rfl,rfl⟩)
      · exact old u v huv
      · exact pendant i b
      · rw [Sym2.eq_swap]
        exact old u v huv
      · rw [Sym2.eq_swap]
        exact pendant i b

end BuyAtBulk.EdgeOnlyGap.ProofB
