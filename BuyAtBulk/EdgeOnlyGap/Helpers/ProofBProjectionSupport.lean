import BuyAtBulk.EdgeOnlyGap.Items.ChainProjection
import BuyAtBulk.EdgeOnlyGap.Items.RouteChain

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap.ProofB

/-- Projection cannot create more supported edges than core edges of the route. -/
theorem projectionSupport (H : FiniteGraph) (q d : ℕ) (π : Lift H q) (hd : 0 < d)
    (r : (supplyData H q d π hd).toInstance.IntegralRouting) (i : Fin (requests H)) :
    (Finset.univ.filter fun e =>
      chainProjection H q d π hd r (routeChain H q d π hd r i) e ≠ 0).card ≤
      coreTraversals H q d π hd r i := by
  classical
  let D := supplyData H q d π hd
  let Y := Finset.univ.filter fun e =>
    chainProjection H q d π hd r (routeChain H q d π hd r i) e ≠ 0
  let C := (D.toInstance.uses (r.path i)).filter (coreResource H q d π hd)
  have hex : ∀ e ∈ Y, ∃ a ∈ C, ∃ j k : Fin q,
      D.location a = Sum.inr (s(Sum.inr (e.val.1,j),Sum.inr (e.val.2,k))) := by
    intro e he
    have hne := (Finset.mem_filter.mp he).2
    change (∑ a, if ∃ j k : Fin q, D.location a.val =
      Sum.inr (s(Sum.inr (e.val.1,j),Sum.inr (e.val.2,k))) then
        routeChain H q d π hd r i a else 0) ≠ 0 at hne
    have hn : ∃ a : {a // a ∈ D.toInstance.usedResources r},
        (if ∃ j k : Fin q, D.location a.val =
          Sum.inr (s(Sum.inr (e.val.1,j),Sum.inr (e.val.2,k))) then
            routeChain H q d π hd r i a else 0) ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (Finset.sum_eq_zero fun a _ => h a)
    obtain ⟨a, ha⟩ := hn
    split_ifs at ha with hloc
    · obtain ⟨j,k,hjk⟩ := hloc
      have huse : a.val ∈ D.toInstance.uses (r.path i) := by
        by_contra h
        exact ha (if_neg h)
      exact ⟨a.val, Finset.mem_filter.mpr ⟨huse, ⟨_, _, hjk⟩⟩, j,k,hjk⟩
    · exact False.elim (ha rfl)
  choose f hf using fun e : Y => hex e.val e.property
  have hinj : Function.Injective (fun e : Y => (⟨f e, (hf e).1⟩ : C)) := by
    intro e₁ e₂ hab
    have hab' : f e₁ = f e₂ := congrArg Subtype.val hab
    obtain ⟨j₁,k₁,h₁⟩ := (hf e₁).2
    obtain ⟨j₂,k₂,h₂⟩ := (hf e₂).2
    rw [hab'] at h₁
    have hh := Sym2.eq_iff.mp (Sum.inr.inj (h₁.symm.trans h₂))
    apply Subtype.ext
    apply Subtype.ext
    rcases hh with ⟨hu,hv⟩ | ⟨hu,hv⟩
    · exact Prod.ext (congrArg (fun v : Fin H.n × Fin q => v.1) (Sum.inr.inj hu))
        (congrArg (fun v : Fin H.n × Fin q => v.1) (Sum.inr.inj hv))
    · have h₁ := congrArg (fun v : Fin H.n × Fin q => v.1) (Sum.inr.inj hu)
      have h₂ := congrArg (fun v : Fin H.n × Fin q => v.1) (Sum.inr.inj hv)
      dsimp only at h₁ h₂
      have := e₁.val.property.1
      have := e₂.val.property.1
      omega
  have hc : Y.card ≤ C.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective _ hinj
  change Y.card ≤ C.card
  exact hc

end BuyAtBulk.EdgeOnlyGap.ProofB
