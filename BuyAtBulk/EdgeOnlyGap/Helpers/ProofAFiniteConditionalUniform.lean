import BuyAtBulk.EdgeOnlyGap.Items.FiniteProbability
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

/-- Equal finite fibers yield the uniform law after conditioning on a positive event. -/
theorem finiteConditionalUniform {Ω α : Type} [Fintype Ω] [Fintype α]
    (E : Ω → Prop) (f : Ω → α) (S : Finset α) (k : α) (hk : k ∈ S)
    (maps : ∀ ω, E ω → f ω ∈ S)
    (uniform : ∀ a ∈ S, Nat.card {ω // E ω ∧ f ω = a} = Nat.card {ω // E ω ∧ f ω = k})
    (positive : 0 < finiteProbability E) :
    finiteProbability (fun ω => E ω ∧ f ω = k) / finiteProbability E = 1 / (S.card : ℝ) := by
  classical
  let F := Finset.univ.filter E
  have he : Nat.card {ω // E ω} = F.card := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, F]
  have hc : F.card = ∑ a ∈ S, (F.filter fun ω => f ω = a).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro ω hω
    exact maps ω (Finset.mem_filter.mp hω).2
  have hf (a : α) : (F.filter fun ω => f ω = a).card = Nat.card {ω // E ω ∧ f ω = a} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext ω
    simp [F, and_assoc]
  have count : Nat.card {ω // E ω} = S.card * Nat.card {ω // E ω ∧ f ω = k} := by
    rw [he, hc]
    simp_rw [hf]
    calc
      (∑ a ∈ S, Nat.card {ω // E ω ∧ f ω = a}) =
          ∑ _a ∈ S, Nat.card {ω // E ω ∧ f ω = k} := by
        apply Finset.sum_congr rfl
        exact uniform
      _ = _ := by simp
  have hΩ : (Nat.card Ω : ℝ) ≠ 0 := by
    intro hn
    simp only [finiteProbability, ← Nat.card_eq_fintype_card, hn, div_zero] at positive
    exact (lt_irrefl 0) positive
  have hE : (Nat.card {ω // E ω} : ℝ) ≠ 0 := by
    intro hn
    simp only [finiteProbability, ← Nat.card_eq_fintype_card, hn, zero_div] at positive
    exact (lt_irrefl 0) positive
  have hS : (S.card : ℝ) ≠ 0 := by
    intro hn
    apply hE
    exact_mod_cast (show Nat.card {ω // E ω} = 0 by
      have : S.card = 0 := by exact_mod_cast hn
      simpa [this] using count)
  unfold finiteProbability
  simp only [← Nat.card_eq_fintype_card]
  rw [div_div_div_cancel_right₀ hΩ]
  apply (div_eq_iff hE).mpr
  have count' := congrArg (fun n : ℕ => (n : ℝ)) count
  simp only [Nat.cast_mul] at count'
  rw [count']
  field_simp [hS]

end BuyAtBulk.EdgeOnlyGap.ProofA
