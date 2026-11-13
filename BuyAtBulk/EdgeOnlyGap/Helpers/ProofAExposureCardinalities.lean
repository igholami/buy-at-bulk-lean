import BuyAtBulk.EdgeOnlyGap.Items.Exposure

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

/-- History size bounds both occupied coordinate sets; consistency equates their sizes. -/
theorem exposureCardinalities (H : FiniteGraph) (q : ℕ) (hist : List (Exposure H q))
    (e : Edges H) :
    (exposedSources H q hist e).card ≤ hist.length ∧
    (exposedTargets H q hist e).card ≤ hist.length ∧
    ∀ π : Lift H q, exposureEvent H q hist π →
      (exposedSources H q hist e).card = (exposedTargets H q hist e).card := by
  classical
  have hs : (exposedSources H q hist e).card ≤ hist.length := by
    unfold exposedSources
    exact (List.toFinset_card_le _).trans (by simp only [List.length_map]; exact List.length_filter_le _ _)
  have ht : (exposedTargets H q hist e).card ≤ hist.length := by
    unfold exposedTargets
    exact (List.toFinset_card_le _).trans (by simp only [List.length_map]; exact List.length_filter_le _ _)
  refine ⟨hs, ht, ?_⟩
  intro π hp
  have hsrc (j : Fin q) : j ∈ exposedSources H q hist e ↔
      ∃ a ∈ hist, a.1 = e ∧ a.2.1 = j := by
    simp only [exposedSources, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
    aesop
  have htgt (k : Fin q) : k ∈ exposedTargets H q hist e ↔
      ∃ a ∈ hist, a.1 = e ∧ a.2.2 = k := by
    simp only [exposedTargets, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
    aesop
  have himg : (exposedSources H q hist e).image (π e) = exposedTargets H q hist e := by
    apply Finset.ext
    intro k
    rw [Finset.mem_image, htgt]
    constructor
    · rintro ⟨j, hj, rfl⟩
      rcases (hsrc j).mp hj with ⟨a, ha, he, hj⟩
      refine ⟨a, ha, he, ?_⟩
      have h := hp a ha
      simpa only [he, hj] using h.symm
    · rintro ⟨a, ha, he, hk⟩
      refine ⟨a.2.1, (hsrc _).mpr ⟨a, ha, he, rfl⟩, ?_⟩
      have h := hp a ha
      simpa only [he, hk] using h
  rw [← himg, Finset.card_image_of_injective _ (π e).injective]

end BuyAtBulk.EdgeOnlyGap.ProofA
