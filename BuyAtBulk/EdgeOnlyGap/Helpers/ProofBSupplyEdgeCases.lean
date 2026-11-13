import BuyAtBulk.EdgeOnlyGap.Items.SupplyData

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofB
attribute [local instance] Classical.propDecidable

/-- Every supply edge is a spoke or projects to one canonically oriented base edge. -/
theorem supplyEdgeCases (H : FiniteGraph) (q : ℕ) (π : Lift H q)
    (s : Sym2 (SupplyVertex H q)) (hs : s ∈ (supplyGraph H q π).edgeSet) :
    (∃ v j, s = s(Sum.inl v, Sum.inr (v,j))) ∨
    (∃ e : Edges H, ∃ j k : Fin q,
      s = s(Sum.inr (e.val.1,j), Sum.inr (e.val.2,k))) := by
  classical
  induction s using Sym2.inductionOn with
  | hf x y =>
    change (supplyGraph H q π).Adj x y at hs
    dsimp [supplyGraph, liftGraph] at hs
    rw [SimpleGraph.fromRel_adj] at hs
    rcases hs.2 with (⟨v,j,rfl,rfl⟩ | ⟨a,b,rfl,rfl,hadj⟩) |
      (⟨v,j,rfl,rfl⟩ | ⟨a,b,rfl,rfl,hadj⟩)
    · exact Or.inl ⟨v,j,rfl⟩
    · rw [SimpleGraph.fromRel_adj] at hadj
      rcases hadj.2 with ⟨e,ha,hb,hk⟩ | ⟨e,hb,ha,hk⟩
      · exact Or.inr ⟨e,a.2,b.2,by rw [← ha, ← hb]⟩
      · exact Or.inr ⟨e,b.2,a.2,by rw [← hb, ← ha, Sym2.eq_swap]⟩
    · exact Or.inl ⟨v,j,Sym2.eq_swap⟩
    · rw [SimpleGraph.fromRel_adj] at hadj
      rcases hadj.2 with ⟨e,hb,ha,hk⟩ | ⟨e,ha,hb,hk⟩
      · exact Or.inr ⟨e,a.2,b.2,by rw [← hb, ← ha, Sym2.eq_swap]⟩
      · exact Or.inr ⟨e,b.2,a.2,by rw [← ha, ← hb]⟩

end BuyAtBulk.EdgeOnlyGap.ProofB
