import BuyAtBulk.EdgeOnlyGap.Items.PrivateLeaves

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofB
attribute [local instance] Classical.propDecidable

/-- The original graph is the induced subgraph on the old vertices. -/
def leafOldEmbedding (D : BuyAtBulk.GraphData) (p : ℚ) (hp : 0 ≤ p) :
    D.graph ↪g (privateLeaves D p hp).graph where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := by
    intro u v
    change (SimpleGraph.fromRel _).Adj (Sum.inl u) (Sum.inl v) ↔ D.graph.Adj u v
    rw [SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨hne,h⟩
      rcases h with (⟨a,b,ha,hb,hab⟩ | ⟨i,c,hi,hc⟩) |
        (⟨a,b,ha,hb,hab⟩ | ⟨i,c,hi,hc⟩)
      · have hua : u = a := Sum.inl.inj ha
        have hvb : v = b := Sum.inl.inj hb
        exact hua.symm ▸ hvb.symm ▸ hab
      · cases hi
      · have hva : v = a := Sum.inl.inj ha
        have hub : u = b := Sum.inl.inj hb
        exact hub.symm ▸ hva.symm ▸ hab.symm
      · cases hi
    · intro h
      exact ⟨fun he => h.ne (Sum.inl.inj he), Or.inl (Or.inl ⟨u,v,rfl,rfl,h⟩)⟩

end BuyAtBulk.EdgeOnlyGap.ProofB
