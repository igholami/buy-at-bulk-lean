import BuyAtBulk.EdgeOnlyGap.Items.SupplyData
import Mathlib.Tactic.Ring

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 5: exact vertex/resource counts, one edge per resource. -/
theorem supplySizes (H : FiniteGraph) (q d : ℕ) (π : Lift H q) (hd : 0 < d) :
  Fintype.card (supplyData H q d π hd).Vertex = H.n*(q+1) ∧
  (supplyData H q d π hd).resourceCount = q*(H.n+requests H) := by
  classical
  refine ⟨?_, ?_⟩
  · change Fintype.card (SupplyVertex H q) = H.n * (q + 1)
    change Fintype.card (Fin H.n ⊕ (Fin H.n × Fin q)) = _
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    ring
  · change Fintype.card (supplyGraph H q π).edgeSet = q * (H.n + requests H)
    let G := supplyGraph H q π
    let f : (Fin H.n × Fin q) ⊕ (Edges H × Fin q) → G.edgeSet := fun x =>
      match x with
      | Sum.inl (v, j) => ⟨s(Sum.inl v, Sum.inr (v, j)), by
          change (supplyGraph H q π).Adj (Sum.inl v) (Sum.inr (v, j))
          dsimp [supplyGraph]
          rw [SimpleGraph.fromRel_adj]
          exact ⟨by simp, Or.inl (Or.inl ⟨v, j, rfl, rfl⟩)⟩⟩
      | Sum.inr (e, j) => ⟨s(Sum.inr (e.val.1, j), Sum.inr (e.val.2, π e j)), by
          change (supplyGraph H q π).Adj (Sum.inr (e.val.1, j)) (Sum.inr (e.val.2, π e j))
          dsimp [supplyGraph, liftGraph]
          rw [SimpleGraph.fromRel_adj]
          have hne : (Sum.inr (e.val.1, j) : SupplyVertex H q) ≠ Sum.inr (e.val.2, π e j) := by
            intro h
            exact ne_of_lt e.prop.1 (congrArg Prod.fst (Sum.inr.inj h))
          refine ⟨hne, Or.inl (Or.inr ⟨(e.val.1, j), (e.val.2, π e j), rfl, rfl, ?_⟩)⟩
          rw [SimpleGraph.fromRel_adj]
          exact ⟨fun h => ne_of_lt e.prop.1 (congrArg Prod.fst h), Or.inl ⟨e, rfl, rfl, rfl⟩⟩⟩
    have hinj : Function.Injective f := by
      intro x y hxy
      have heq := congrArg Subtype.val hxy
      rcases x with ⟨v₁, j₁⟩ | ⟨e₁, j₁⟩ <;> rcases y with ⟨v₂, j₂⟩ | ⟨e₂, j₂⟩
      · simp only [f, Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq] at heq
        rcases heq with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact congrArg Sum.inl h2
        · cases h1
      · simp only [f, Sym2.eq_iff] at heq
        rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩ <;> cases h1
      · simp only [f, Sym2.eq_iff] at heq
        rcases heq with ⟨h1, _⟩ | ⟨_, h2⟩
        · cases h1
        · cases h2
      · simp only [f, Sym2.eq_iff, Sum.inr.injEq, Prod.mk.injEq] at heq
        rcases heq with ⟨⟨hu, hj⟩, ⟨hv, _⟩⟩ | ⟨⟨h1, _⟩, ⟨h2, _⟩⟩
        · congr 1
          exact Prod.ext (Subtype.ext (Prod.ext hu hv)) hj
        · have := e₁.prop.1
          have := e₂.prop.1
          omega
    have hsurj : Function.Surjective f := by
      intro ⟨s, hs⟩
      induction s using Sym2.inductionOn with
      | hf x y =>
        change (supplyGraph H q π).Adj x y at hs
        dsimp [supplyGraph, liftGraph] at hs
        rw [SimpleGraph.fromRel_adj] at hs
        rcases hs.2 with (⟨v, j, rfl, rfl⟩ | ⟨a, b, rfl, rfl, hadj⟩) |
                         (⟨v, j, rfl, rfl⟩ | ⟨a, b, rfl, rfl, hadj⟩)
        · exact ⟨Sum.inl (v, j), rfl⟩
        · rw [SimpleGraph.fromRel_adj] at hadj
          rcases hadj.2 with ⟨e, ha1, hb1, hb2⟩ | ⟨e, hb1, ha1, ha2⟩
          · refine ⟨Sum.inr (e, a.2), Subtype.ext ?_⟩
            dsimp [f]
            rw [← ha1, ← hb1, ← hb2]
          · refine ⟨Sum.inr (e, b.2), Subtype.ext ?_⟩
            dsimp [f]
            rw [← hb1, ← ha1, ← ha2, Sym2.eq_swap]
        · refine ⟨Sum.inl (v, j), Subtype.ext ?_⟩
          dsimp [f]
          exact Sym2.eq_swap
        · rw [SimpleGraph.fromRel_adj] at hadj
          rcases hadj.2 with ⟨e, hb1, ha1, ha2⟩ | ⟨e, ha1, hb1, hb2⟩
          · refine ⟨Sum.inr (e, a.2), Subtype.ext ?_⟩
            dsimp [f]
            rw [← hb1, ← ha1, ← ha2, Sym2.eq_swap]
          · refine ⟨Sum.inr (e, b.2), Subtype.ext ?_⟩
            dsimp [f]
            rw [← ha1, ← hb1, ← hb2]
    rw [← Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)]
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    unfold requests
    ring

end BuyAtBulk.EdgeOnlyGap
