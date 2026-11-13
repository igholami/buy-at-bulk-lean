import BuyAtBulk.EdgeOnlyGap.Items.Exposure
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofAExposureCardinalities
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofAMatchingFiberCard
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofAFiniteConditionalUniform

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 2: uniform fresh mate, both traversal directions, ≥q−T available vertices. -/
theorem conditionalMatching (H : FiniteGraph) (q T : ℕ) (hist : List (Exposure H q))
    (earlier : hist.length < T) (e : Edges H)
    (positive : 0 < liftProbability H q (exposureEvent H q hist)) :
  q-T ≤ (Finset.univ \ exposedTargets H q hist e).card ∧
  q-T ≤ (Finset.univ \ exposedSources H q hist e).card ∧
  (∀ j, j ∉ exposedSources H q hist e → ∀ k, k ∉ exposedTargets H q hist e →
    conditionalLiftProbability H q (exposureEvent H q hist) (fun π => π e j=k) =
      1/((Finset.univ \ exposedTargets H q hist e).card:ℝ)) ∧
  (∀ k, k ∉ exposedTargets H q hist e → ∀ j, j ∉ exposedSources H q hist e →
    conditionalLiftProbability H q (exposureEvent H q hist) (fun π => (π e).symm k=j) =
      1/((Finset.univ \ exposedSources H q hist e).card:ℝ)) := by
  classical
  have hc := ProofA.exposureCardinalities H q hist e
  have hct : q - T ≤ (Finset.univ \ exposedTargets H q hist e).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  have hcs : q - T ≤ (Finset.univ \ exposedSources H q hist e).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  have hfor : ∀ j, j ∉ exposedSources H q hist e → ∀ k, k ∉ exposedTargets H q hist e →
      conditionalLiftProbability H q (exposureEvent H q hist) (fun π => π e j = k) =
        1 / ((Finset.univ \ exposedTargets H q hist e).card : ℝ) := by
    intro j hj k hk
    let A := Finset.univ \ exposedTargets H q hist e
    have hkA : k ∈ A := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hk⟩
    have hmaps : ∀ π : Lift H q, exposureEvent H q hist π → π e j ∈ A := by
      intro π hp
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro htarget
      simp only [exposedTargets, List.mem_toFinset, List.mem_map, List.mem_filter,
        decide_eq_true_eq] at htarget
      rcases htarget with ⟨a, ⟨ha, he⟩, ht⟩
      have hpair : π e a.2.1 = π e j := by
        simpa only [he, ht] using hp a ha
      have hj' := (π e).injective hpair
      apply hj
      simp only [exposedSources, List.mem_toFinset, List.mem_map, List.mem_filter,
        decide_eq_true_eq]
      exact ⟨a, ⟨ha, he⟩, hj'⟩
    have hunif : ∀ a ∈ A,
        Nat.card {π : Lift H q // exposureEvent H q hist π ∧ π e j = a} =
          Nat.card {π : Lift H q // exposureEvent H q hist π ∧ π e j = k} := by
      intro a ha
      exact ProofA.matchingFiberCard H q hist e j a k (Finset.mem_sdiff.mp ha).2 hk
    exact ProofA.finiteConditionalUniform (exposureEvent H q hist) (fun π => π e j)
      A k hkA hmaps hunif positive
  refine ⟨hct, hcs, hfor, ?_⟩
  have hex : ∃ π : Lift H q, exposureEvent H q hist π := by
    by_contra hn
    push_neg at hn
    haveI : IsEmpty {π : Lift H q // exposureEvent H q hist π} := ⟨fun π => hn π.val π.prop⟩
    have h0 : Nat.card {π : Lift H q // exposureEvent H q hist π} = 0 := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_eq_zero
    simp only [liftProbability, finiteProbability, ← Nat.card_eq_fintype_card,
      h0, Nat.cast_zero, zero_div] at positive
    exact (lt_irrefl 0) positive
  obtain ⟨π, hp⟩ := hex
  have hcards : (Finset.univ \ exposedTargets H q hist e).card =
      (Finset.univ \ exposedSources H q hist e).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_sdiff_of_subset (Finset.subset_univ _), hc.2.2 π hp]
  intro k hk j hj
  have hevents : (fun π : Lift H q => (π e).symm k = j) = (fun π => π e j = k) := by
    funext π
    exact propext ((π e).symm_apply_eq.trans eq_comm)
  rw [hevents, hfor j hj k hk, hcards]


end BuyAtBulk.EdgeOnlyGap
