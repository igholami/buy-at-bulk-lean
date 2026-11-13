import BuyAtBulk.EdgeOnlyGap.Items.Edges

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Pp. 1–3, implicit representation adapter: canonical ordered edge
coordinates count the existing Mathlib undirected edges. Used only to transport
Mathlib's degree-sum formula; no independent handshaking result is assumed. -/
theorem edgeCard (H : FiniteGraph) :
    Fintype.card (Edges H) = H.graph.edgeFinset.card := by
  classical
  let f : Edges H → H.graph.edgeSet := fun e => ⟨s(e.val.1, e.val.2), e.prop.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have eq := Sym2.eq_iff.mp (congrArg Subtype.val hab)
    rcases eq with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Subtype.ext (Prod.ext h₁ h₂)
    · have ha := a.prop.1
      have hb := b.prop.1
      omega
  have hsurj : Function.Surjective f := by
    intro e
    obtain ⟨e, he⟩ := e
    induction e using Sym2.inductionOn with
    | hf u v =>
      have adj : H.graph.Adj u v := he
      rcases lt_or_gt_of_ne adj.ne with huv | hvu
      · exact ⟨⟨(u, v), huv, adj⟩, rfl⟩
      · refine ⟨⟨(v, u), hvu, adj.symm⟩, ?_⟩
        apply Subtype.ext
        exact Sym2.eq_swap
  exact (Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).trans H.graph.card_edgeSet

end BuyAtBulk.EdgeOnlyGap
