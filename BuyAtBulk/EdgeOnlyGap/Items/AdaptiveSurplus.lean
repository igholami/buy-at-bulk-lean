import BuyAtBulk.EdgeOnlyGap.Items.AdaptiveExploration
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofAAdaptiveHit

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Adaptive product bound, p. 2: prescribed surplus events with target sets determined by prior information. -/
theorem adaptiveSurplus (H : FiniteGraph) (q T : ℕ) (policy : AdaptivePolicy H q T)
    (old : List (Exposure H q) → Finset (Fin q)) (small : ∀ hist, (old hist).card ≤ T+1)
    (hT : 4 ≤ T) (hq : 8*T ≤ q) (times : Finset (Fin T)) :
  liftProbability H q (fun π => ∀ t ∈ times,
    let hist := adaptiveTranscript H q T policy π t.val
    ∃ e rev j, hist.length < T ∧ policy.next hist = some (e,rev,j) ∧
      (if rev then (π e).symm j else π e j) ∈ old hist) ≤
    (4*T/(q:ℝ))^times.card := by
  classical
  change finiteProbability (fun π => ∀ t ∈ times,
    ProofA.adaptiveHit H q T policy old t.val π) ≤ _
  induction times using Finset.induction_on_max with
  | empty =>
    simpa using (ProofA.probability_le_one
      (fun π : Lift H q => ∀ t ∈ (∅ : Finset (Fin T)), ProofA.adaptiveHit H q T policy old t.val π))
  | insert a s hmax ih =>
    have hnot : a ∉ s := by intro ha; exact lt_irrefl a (hmax a ha)
    let A := ProofA.adaptiveHit H q T policy old a.val
    let B := fun π => ∀ t ∈ s, ProofA.adaptiveHit H q T policy old t.val π
    let f := fun π => adaptiveTranscript H q T policy π a.val
    have hmeas : ∀ π ρ, f π = f ρ → (B π ↔ B ρ) := by
      intro π ρ heq
      apply forall₂_congr
      intro t ht
      exact ProofA.adaptiveHit_measurable H q T policy old π ρ (hmax t ht) heq
    have hbound : ∀ hist ∈ Finset.univ.image f,
        finiteProbability (fun π => f π = hist ∧ A π) ≤
          (4*T/(q:ℝ)) * finiteProbability (fun π => f π = hist) := by
      intro hist hhist
      obtain ⟨π, _, rfl⟩ := Finset.mem_image.mp hhist
      have hfiber (ρ : Lift H q) : f ρ = f π ↔
          exposureEvent H q (adaptiveTranscript H q T policy π a.val) ρ :=
        ProofA.transcript_fiber H q T policy π ρ a.val
      calc
        finiteProbability (fun ρ => f ρ = f π ∧ A ρ) =
            finiteProbability (fun ρ => exposureEvent H q (adaptiveTranscript H q T policy π a.val) ρ ∧ A ρ) :=
          ProofA.probability_congr (fun ρ => and_congr_left (fun _ => hfiber ρ))
        _ ≤ (4*T/(q:ℝ)) * finiteProbability
            (exposureEvent H q (adaptiveTranscript H q T policy π a.val)) :=
          ProofA.adaptiveHit_mass H q T policy old small hT hq π a.val
        _ = (4*T/(q:ℝ)) * finiteProbability (fun ρ => f ρ = f π) := by
          congr 1
          exact ProofA.probability_congr (fun ρ => (hfiber ρ).symm)
    calc
      finiteProbability (fun π => ∀ t ∈ insert a s,
          ProofA.adaptiveHit H q T policy old t.val π) =
          finiteProbability (fun π => B π ∧ A π) := by
        apply ProofA.probability_congr
        intro π
        simp [B, A, and_comm]
      _ ≤ (4*T/(q:ℝ)) * finiteProbability B :=
        ProofA.probability_conditioned_step A B f _ hmeas hbound
      _ ≤ (4*T/(q:ℝ)) * (4*T/(q:ℝ))^s.card :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = (4*T/(q:ℝ))^(insert a s).card := by
        rw [Finset.card_insert_of_notMem hnot, pow_succ]
        exact mul_comm _ _

end BuyAtBulk.EdgeOnlyGap
