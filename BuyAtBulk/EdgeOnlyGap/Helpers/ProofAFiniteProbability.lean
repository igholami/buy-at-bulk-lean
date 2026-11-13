import BuyAtBulk.EdgeOnlyGap.Items.FiniteProbability
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

 theorem probability_congr {Ω : Type} [Fintype Ω] {E F : Ω → Prop}
    (h : ∀ ω, E ω ↔ F ω) : finiteProbability E = finiteProbability F := by
  congr 1
  funext ω
  exact propext (h ω)

 theorem probability_nonneg {Ω : Type} [Fintype Ω] (E : Ω → Prop) :
    0 ≤ finiteProbability E := by unfold finiteProbability; positivity

 theorem probability_mono {Ω : Type} [Fintype Ω] {E F : Ω → Prop}
    (h : ∀ ω, E ω → F ω) : finiteProbability E ≤ finiteProbability F := by
  unfold finiteProbability
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Fintype.card_le_of_injective
    (fun x : {ω // E ω} => (⟨x.1, h x.1 x.2⟩ : {ω // F ω}))
    (by intro x y he; apply Subtype.ext; exact congrArg (fun z : {ω // F ω} => z.val) he)

 theorem probability_le_one {Ω : Type} [Fintype Ω] (E : Ω → Prop) :
    finiteProbability E ≤ 1 := by
  unfold finiteProbability
  apply div_le_one_of_le₀ _ (by positivity)
  exact_mod_cast Fintype.card_subtype_le E

 theorem probability_partition {Ω α : Type} [Fintype Ω] [DecidableEq α]
    (E : Ω → Prop) (f : Ω → α) :
    finiteProbability E = ∑ a ∈ Finset.univ.image f,
      finiteProbability (fun ω => E ω ∧ f ω = a) := by
  classical
  let S := Finset.univ.filter E
  have hc : S.card = ∑ a ∈ Finset.univ.image f, (S.filter fun ω => f ω = a).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro ω hω
    exact Finset.mem_image.mpr ⟨ω, Finset.mem_univ _, rfl⟩
  have he : Fintype.card {ω // E ω} = S.card := by
    simp [S, Fintype.card_subtype]
  have hf (a : α) : Fintype.card {ω // E ω ∧ f ω = a} =
      (S.filter fun ω => f ω = a).card := by
    simp only [Fintype.card_subtype]
    congr 1
    ext ω
    simp [S, and_assoc]
  unfold finiteProbability
  rw [he, hc, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  dsimp only
  simp only [← Nat.card_eq_fintype_card] at hf ⊢
  rw [hf]

/-- A fiberwise conditional bound applies after any event measurable on those fibers.
The mass formulation includes fibers of probability zero. -/
 theorem probability_conditioned_step {Ω α : Type} [Fintype Ω] [DecidableEq α]
    (A B : Ω → Prop) (f : Ω → α) (p : ℝ)
    (measurable : ∀ ω ρ, f ω = f ρ → (B ω ↔ B ρ))
    (bound : ∀ a ∈ Finset.univ.image f,
      finiteProbability (fun ω => f ω = a ∧ A ω) ≤
        p * finiteProbability (fun ω => f ω = a)) :
    finiteProbability (fun ω => B ω ∧ A ω) ≤ p * finiteProbability B := by
  rw [probability_partition (fun ω => B ω ∧ A ω) f,
      probability_partition B f, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  obtain ⟨ρ, _, rfl⟩ := Finset.mem_image.mp ha
  by_cases hb : B ρ
  · have hleft : finiteProbability (fun ω => (B ω ∧ A ω) ∧ f ω = f ρ) =
        finiteProbability (fun ω => f ω = f ρ ∧ A ω) := by
      apply probability_congr
      intro ω
      constructor
      · tauto
      · rintro ⟨hf, hA⟩
        exact ⟨⟨(measurable ω ρ hf).mpr hb, hA⟩, hf⟩
    have hright : finiteProbability (fun ω => B ω ∧ f ω = f ρ) =
        finiteProbability (fun ω => f ω = f ρ) := by
      apply probability_congr
      intro ω
      exact ⟨And.right, fun hf => ⟨(measurable ω ρ hf).mpr hb, hf⟩⟩
    rw [hleft, hright]
    exact bound _ (Finset.mem_image.mpr ⟨ρ, Finset.mem_univ _, rfl⟩)
  · have hzero (ω) (hf : f ω = f ρ) : ¬B ω := by
      exact fun hω => hb ((measurable ω ρ hf).mp hω)
    have hl : finiteProbability (fun ω => (B ω ∧ A ω) ∧ f ω = f ρ) = 0 := by
      unfold finiteProbability
      have : IsEmpty {ω // (B ω ∧ A ω) ∧ f ω = f ρ} :=
        ⟨fun ω => hzero ω.1 ω.2.2 ω.2.1.1⟩
      simp
    have hr : finiteProbability (fun ω => B ω ∧ f ω = f ρ) = 0 := by
      unfold finiteProbability
      have : IsEmpty {ω // B ω ∧ f ω = f ρ} :=
        ⟨fun ω => hzero ω.1 ω.2.2 ω.2.1⟩
      simp
    rw [hl, hr, mul_zero]

end BuyAtBulk.EdgeOnlyGap.ProofA
