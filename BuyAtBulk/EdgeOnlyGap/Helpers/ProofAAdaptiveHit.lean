import BuyAtBulk.EdgeOnlyGap.Helpers.ProofAAdaptiveTranscript
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofAFiniteProbability
import BuyAtBulk.EdgeOnlyGap.Items.SurplusProbability

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

/-- The actual surplus event at one query time, with the original stopping semantics. -/
def adaptiveHit (H : FiniteGraph) (q T : ℕ) (policy : AdaptivePolicy H q T)
    (old : List (Exposure H q) → Finset (Fin q)) (n : ℕ) (π : Lift H q) : Prop :=
  let hist := adaptiveTranscript H q T policy π n
  ∃ e rev j, hist.length < T ∧ policy.next hist = some (e,rev,j) ∧
    (if rev then (π e).symm j else π e j) ∈ old hist

 theorem transcript_query_agreement (H : FiniteGraph) (q T : ℕ)
    (policy : AdaptivePolicy H q T) (π ρ : Lift H q) (n : ℕ)
    (e : Edges H) (rev : Bool) (j : Fin q)
    (hlen : (adaptiveTranscript H q T policy π n).length < T)
    (hn : policy.next (adaptiveTranscript H q T policy π n) = some (e,rev,j))
    (h : exposureEvent H q (adaptiveTranscript H q T policy π (n+1)) ρ) :
    (if rev then (ρ e).symm j else ρ e j) =
      (if rev then (π e).symm j else π e j) := by
  have hout := h (if rev then (e, (π e).symm j, j) else (e,j,π e j)) (by
    simp [adaptiveTranscript, hlen, hn])
  cases rev
  · exact hout
  · exact (Equiv.symm_apply_eq (ρ e)).mpr hout.symm

 theorem adaptiveHit_transfer (H : FiniteGraph) (q T : ℕ)
    (policy : AdaptivePolicy H q T) (old : List (Exposure H q) → Finset (Fin q))
    (π ρ : Lift H q) (n : ℕ)
    (h : exposureEvent H q (adaptiveTranscript H q T policy π (n+1)) ρ)
    (hit : adaptiveHit H q T policy old n π) : adaptiveHit H q T policy old n ρ := by
  have hp : exposureEvent H q (adaptiveTranscript H q T policy π n) ρ :=
    fun a ha => h a (transcript_mono H q T policy π (Nat.le_succ n) a ha)
  have heq := transcript_agreement H q T policy π ρ n hp
  rcases hit with ⟨e,rev,j,hlen,hn,hold⟩
  change ∃ e rev j, _
  rw [heq]
  refine ⟨e,rev,j,hlen,hn,?_⟩
  rw [transcript_query_agreement H q T policy π ρ n e rev j hlen hn h]
  exact hold

 theorem adaptiveHit_measurable (H : FiniteGraph) (q T : ℕ)
    (policy : AdaptivePolicy H q T) (old : List (Exposure H q) → Finset (Fin q))
    (π ρ : Lift H q) {k n : ℕ} (hkn : k < n)
    (heq : adaptiveTranscript H q T policy π n = adaptiveTranscript H q T policy ρ n) :
    adaptiveHit H q T policy old k π ↔ adaptiveHit H q T policy old k ρ := by
  have hf : exposureEvent H q (adaptiveTranscript H q T policy π (k+1)) ρ := by
    intro a ha
    have hm := transcript_mono H q T policy π hkn a ha
    rw [heq] at hm
    exact transcript_consistent H q T policy ρ n a hm
  have hr : exposureEvent H q (adaptiveTranscript H q T policy ρ (k+1)) π := by
    intro a ha
    have hm := transcript_mono H q T policy ρ hkn a ha
    rw [← heq] at hm
    exact transcript_consistent H q T policy π n a hm
  exact ⟨adaptiveHit_transfer H q T policy old π ρ k hf,
    adaptiveHit_transfer H q T policy old ρ π k hr⟩

 theorem adaptiveHit_mass (H : FiniteGraph) (q T : ℕ)
    (policy : AdaptivePolicy H q T) (old : List (Exposure H q) → Finset (Fin q))
    (small : ∀ hist, (old hist).card ≤ T+1) (hT : 4 ≤ T) (hq : 8*T ≤ q)
    (π : Lift H q) (n : ℕ) :
    liftProbability H q (fun ρ => exposureEvent H q (adaptiveTranscript H q T policy π n) ρ ∧
      adaptiveHit H q T policy old n ρ) ≤
      (4*T/(q:ℝ)) * liftProbability H q (exposureEvent H q (adaptiveTranscript H q T policy π n)) := by
  let hist := adaptiveTranscript H q T policy π n
  let E := exposureEvent H q hist
  have hpnonneg : 0 ≤ (4*T/(q:ℝ)) := by positivity
  by_cases hp : 0 < liftProbability H q E
  · by_cases hlen : hist.length < T
    · cases hn : policy.next hist with
      | none =>
        have hz : liftProbability H q (fun ρ => E ρ ∧ adaptiveHit H q T policy old n ρ) = 0 := by
          change finiteProbability _ = 0
          have he : (fun ρ => E ρ ∧ adaptiveHit H q T policy old n ρ) = (fun _ => False) := by
            funext ρ
            apply propext
            constructor
            · rintro ⟨hE, e,rev,j,_,hnext,_⟩
              have heq := transcript_agreement H q T policy π ρ n hE
              rw [heq] at hnext
              change policy.next hist = _ at hnext
              simp only [hn, reduceCtorEq] at hnext
            · simp
          rw [he]
          simp [finiteProbability]
        change liftProbability H q (fun ρ => E ρ ∧ adaptiveHit H q T policy old n ρ) ≤ _
        rw [hz]
        exact mul_nonneg hpnonneg (le_of_lt hp)
      | some a =>
        rcases a with ⟨e,rev,j⟩
        have hsub : liftProbability H q (fun ρ => E ρ ∧ adaptiveHit H q T policy old n ρ) ≤
            liftProbability H q (fun ρ => E ρ ∧ (if rev then (ρ e).symm j else ρ e j) ∈ old hist) := by
          apply probability_mono
          rintro ρ ⟨hE, e',rev',j',hlen',hn',hold⟩
          have heq := transcript_agreement H q T policy π ρ n hE
          rw [heq] at hn' hold
          change policy.next hist = _ at hn'
          rw [hn] at hn'
          cases Option.some.inj hn'
          exact ⟨hE,hold⟩
        have hbound := surplusProbability H q T hist e (old hist) hlen (small hist) hT hq hp
        have hfresh := policy.fresh hist e rev j hlen hn
        have hc : conditionalLiftProbability H q E
            (fun ρ => (if rev then (ρ e).symm j else ρ e j) ∈ old hist) ≤ 4*T/(q:ℝ) := by
          cases rev
          · exact hbound.1 j hfresh
          · exact hbound.2 j hfresh
        exact hsub.trans ((div_le_iff₀ hp).mp hc)
    · have hz : liftProbability H q (fun ρ => E ρ ∧ adaptiveHit H q T policy old n ρ) = 0 := by
        change finiteProbability _ = 0
        have he : (fun ρ => E ρ ∧ adaptiveHit H q T policy old n ρ) = (fun _ => False) := by
          funext ρ
          apply propext
          constructor
          · rintro ⟨hE,e,rev,j,hlen',_⟩
            have heq := transcript_agreement H q T policy π ρ n hE
            rw [heq] at hlen'
            exact hlen hlen'
          · simp
        rw [he]
        simp [finiteProbability]
      change liftProbability H q (fun ρ => E ρ ∧ adaptiveHit H q T policy old n ρ) ≤ _
      rw [hz]
      exact mul_nonneg hpnonneg (le_of_lt hp)
  · have hezero : liftProbability H q E = 0 :=
      le_antisymm (le_of_not_gt hp) (probability_nonneg E)
    have hsub : liftProbability H q (fun ρ => E ρ ∧ adaptiveHit H q T policy old n ρ) ≤
        liftProbability H q E := probability_mono (fun _ h => h.1)
    change liftProbability H q (fun ρ => E ρ ∧ adaptiveHit H q T policy old n ρ) ≤ _
    rw [hezero, mul_zero]
    exact hezero ▸ hsub

end BuyAtBulk.EdgeOnlyGap.ProofA
