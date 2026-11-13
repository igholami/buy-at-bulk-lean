import BuyAtBulk.EdgeOnlyGap.Items.Exposure

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

/-- Swapping two unexposed targets bijects the corresponding conditioned matching fibers. -/
theorem matchingFiberCard (H : FiniteGraph) (q : ℕ) (hist : List (Exposure H q))
    (e : Edges H) (j k l : Fin q)
    (hk : k ∉ exposedTargets H q hist e) (hl : l ∉ exposedTargets H q hist e) :
    Nat.card {π : Lift H q // exposureEvent H q hist π ∧ π e j = k} =
      Nat.card {π : Lift H q // exposureEvent H q hist π ∧ π e j = l} := by
  classical
  let f : Lift H q → Lift H q := fun π a =>
    if a = e then (π a).trans (Equiv.swap k l) else π a
  have hff : ∀ π, f (f π) = π := by
    intro π
    funext a
    by_cases ha : a = e
    · apply Equiv.ext
      intro x
      simp only [f, if_pos ha, Equiv.trans_apply, Equiv.swap_apply_self]
    · simp only [f, if_neg ha]
  have hpres : ∀ π, exposureEvent H q hist π → exposureEvent H q hist (f π) := by
    intro π hp a ha
    by_cases he : a.1 = e
    · have htarget : a.2.2 ∈ exposedTargets H q hist e := by
        simp only [exposedTargets, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
        exact ⟨a, ⟨ha, he⟩, rfl⟩
      have hka : a.2.2 ≠ k := fun h => hk (h ▸ htarget)
      have hla : a.2.2 ≠ l := fun h => hl (h ▸ htarget)
      change (f π a.1) a.2.1 = a.2.2
      simp only [f, if_pos he, Equiv.trans_apply]
      rw [hp a ha, Equiv.swap_apply_of_ne_of_ne hka hla]
    · change (f π a.1) a.2.1 = a.2.2
      simpa only [f, if_neg he] using hp a ha
  let s : Lift H q ≃ Lift H q := ⟨f, f, hff, hff⟩
  apply Nat.card_congr
  apply Equiv.subtypeEquiv s
  intro π
  change (exposureEvent H q hist π ∧ π e j = k) ↔
    (exposureEvent H q hist (f π) ∧ f π e j = l)
  constructor
  · rintro ⟨hp, hj⟩
    refine ⟨hpres π hp, ?_⟩
    simp only [f, if_pos rfl, Equiv.trans_apply, hj, Equiv.swap_apply_left]
  · rintro ⟨hp, hj⟩
    refine ⟨?_, ?_⟩
    · simpa only [hff] using hpres (f π) hp
    · have h := congrArg (Equiv.swap k l) hj
      simpa only [f, if_pos rfl, Equiv.trans_apply, Equiv.swap_apply_self,
        Equiv.swap_apply_right] using h

end BuyAtBulk.EdgeOnlyGap.ProofA
