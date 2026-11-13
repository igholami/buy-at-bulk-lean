import BuyAtBulk.EdgeOnlyGap.Items.AdaptiveExploration
import Mathlib.Tactic

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

 theorem transcript_consistent (H : FiniteGraph) (q T : ℕ)
    (policy : AdaptivePolicy H q T) (π : Lift H q) (n : ℕ) :
    exposureEvent H q (adaptiveTranscript H q T policy π n) π := by
  induction n with
  | zero => simp [adaptiveTranscript, exposureEvent]
  | succ n ih =>
    simp only [adaptiveTranscript]
    split
    · cases hn : policy.next (adaptiveTranscript H q T policy π n) with
      | none => exact ih
      | some a =>
        rcases a with ⟨e, rev, j⟩
        intro a ha
        simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · exact ih a ha
        · cases rev <;> simp
    · exact ih

 theorem transcript_mono (H : FiniteGraph) (q T : ℕ)
    (policy : AdaptivePolicy H q T) (π : Lift H q) {m n : ℕ} (hmn : m ≤ n) :
    ∀ a ∈ adaptiveTranscript H q T policy π m,
      a ∈ adaptiveTranscript H q T policy π n := by
  induction n, hmn using Nat.le_induction with
  | base => exact fun _ ha => ha
  | succ n hmn ih =>
    intro a ha
    have h := ih a ha
    simp only [adaptiveTranscript]
    split
    · split <;> simp_all
    · exact h

 theorem transcript_agreement (H : FiniteGraph) (q T : ℕ)
    (policy : AdaptivePolicy H q T) (π ρ : Lift H q) (n : ℕ)
    (h : exposureEvent H q (adaptiveTranscript H q T policy π n) ρ) :
    adaptiveTranscript H q T policy ρ n = adaptiveTranscript H q T policy π n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp : exposureEvent H q (adaptiveTranscript H q T policy π n) ρ :=
      fun a ha => h a (transcript_mono H q T policy π (Nat.le_succ n) a ha)
    have heq := ih hp
    simp only [adaptiveTranscript, heq]
    split
    · rename_i hlen
      cases hn : policy.next (adaptiveTranscript H q T policy π n) with
      | none => rfl
      | some a =>
        rcases a with ⟨e, rev, j⟩
        have hout := h (if rev then (e, (π e).symm j, j) else (e,j,π e j)) (by
          simp [adaptiveTranscript, hlen, hn])
        cases rev
        · simpa only [Bool.false_eq_true, ↓reduceIte] using
            congrArg (fun k => adaptiveTranscript H q T policy π n ++ [(e,j,k)]) hout
        · have hv : (ρ e).symm j = (π e).symm j := by
            exact (Equiv.symm_apply_eq (ρ e)).mpr hout.symm
          simp only [Bool.true_eq, ↓reduceIte, hv]
    · rfl

 theorem transcript_fiber (H : FiniteGraph) (q T : ℕ)
    (policy : AdaptivePolicy H q T) (π ρ : Lift H q) (n : ℕ) :
    adaptiveTranscript H q T policy ρ n = adaptiveTranscript H q T policy π n ↔
      exposureEvent H q (adaptiveTranscript H q T policy π n) ρ := by
  constructor
  · intro h
    rw [← h]
    exact transcript_consistent H q T policy ρ n
  · exact transcript_agreement H q T policy π ρ n

 theorem transcript_length (H : FiniteGraph) (q T : ℕ)
    (policy : AdaptivePolicy H q T) (π : Lift H q) (n : ℕ) :
    (adaptiveTranscript H q T policy π n).length ≤ n := by
  induction n with
  | zero => simp [adaptiveTranscript]
  | succ n ih =>
    simp only [adaptiveTranscript]
    split
    · cases hn : policy.next (adaptiveTranscript H q T policy π n) with
      | none => exact Nat.le_trans ih (Nat.le_succ n)
      | some a => simpa using Nat.succ_le_succ ih
    · omega

end BuyAtBulk.EdgeOnlyGap.ProofA
