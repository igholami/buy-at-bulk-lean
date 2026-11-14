import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBSupplyEdgeCases
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBCollapseEdge

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap.ProofB
attribute [local instance] Classical.propDecidable

/-- Boundary commutation on a single supply edge, including spoke cancellation. -/
theorem projectionColumn (H : FiniteGraph) (q : ℕ) (π : Lift H q)
    (a : Sym2 (SupplyVertex H q)) (ha : a ∈ (supplyGraph H q π).edgeSet)
    (v : Fin H.n) (z : ZMod 2) :
    (∑ e : Edges H, if v = e.val.1 ∨ v = e.val.2 then
      (if ∃ j k : Fin q, a = s(Sum.inr (e.val.1,j),Sum.inr (e.val.2,k))
        then z else 0) else 0) =
    ∑ w : SupplyVertex H q, if collapseVertex H q w = v then
      (if w ∈ a then z else 0) else 0 := by
  classical
  rcases supplyEdgeCases H q π a ha with ⟨u,j,rfl⟩ | ⟨e,j,k,rfl⟩
  · have hm (e : Edges H) : ¬ ∃ j' k' : Fin q,
        s(Sum.inl u, Sum.inr (u,j)) =
          s(Sum.inr (e.val.1,j'), Sum.inr (e.val.2,k')) := by
      rintro ⟨j',k',h⟩
      rcases Sym2.eq_iff.mp h with ⟨h,_⟩ | ⟨h,_⟩ <;> cases h
    refine Eq.trans ?_ (collapseEdgeBoundary (collapseVertex H q)
      (Sum.inl u) (Sum.inr (u,j)) (by simp) v z).symm
    simp only [hm, if_false, ite_self, Finset.sum_const_zero, collapseVertex]
    by_cases huv : u = v <;> simp [huv, CharTwo.add_self_eq_zero]
  · have hm (b : Edges H) : (∃ j' k' : Fin q,
        s((Sum.inr (e.val.1,j) : SupplyVertex H q), Sum.inr (e.val.2,k)) =
          s(Sum.inr (b.val.1,j'), Sum.inr (b.val.2,k'))) ↔ b = e := by
      constructor
      · rintro ⟨j',k',h⟩
        apply Subtype.ext
        rcases Sym2.eq_iff.mp h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
        · have he₁ : e.val.1 = b.val.1 := congrArg (fun x : Fin H.n × Fin q => x.1) (Sum.inr.inj h₁)
          have he₂ : e.val.2 = b.val.2 := congrArg (fun x : Fin H.n × Fin q => x.1) (Sum.inr.inj h₂)
          exact Prod.ext he₁.symm he₂.symm
        · have hh₁ := congrArg (fun x : Fin H.n × Fin q => x.1) (Sum.inr.inj h₁)
          have hh₂ := congrArg (fun x : Fin H.n × Fin q => x.1) (Sum.inr.inj h₂)
          have he := e.property.1
          have hb := b.property.1
          dsimp only at hh₁ hh₂
          omega
      · rintro rfl
        exact ⟨j,k,rfl⟩
    have hne : (Sum.inr (e.val.1,j) : SupplyVertex H q) ≠ Sum.inr (e.val.2,k) := by
      intro h
      exact (ne_of_lt e.property.1) (congrArg (fun x : Fin H.n × Fin q => x.1) (Sum.inr.inj h))
    refine Eq.trans ?_ (collapseEdgeBoundary (collapseVertex H q)
      (Sum.inr (e.val.1,j)) (Sum.inr (e.val.2,k)) hne v z).symm
    simp_rw [hm]
    rw [Finset.sum_eq_single e]
    · simp only [ite_true, collapseVertex]
      have he := ne_of_lt e.property.1
      by_cases h₁ : v = e.val.1 <;> by_cases h₂ : v = e.val.2 <;>
        simp_all [eq_comm]
    · intro b hb hbe
      simp [hbe]
    · simp

end BuyAtBulk.EdgeOnlyGap.ProofB
