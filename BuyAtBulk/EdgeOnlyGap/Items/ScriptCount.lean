import Mathlib.SetTheory.Cardinal.Finite
import BuyAtBulk.EdgeOnlyGap.Items.DFSScript
import BuyAtBulk.EdgeOnlyGap.Items.Parameters

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 2: variable-length scripts; alphabet 2d+1. -/
theorem scriptCount (d m : ℕ) (hd : 4 ≤ d) (hm : 1 ≤ m) :
  Nat.card (DFSSymbol d) = 2*d+1 ∧
  Nat.card {s : List (DFSSymbol d) // s.length ≤ 2*m} ≤ (4*d)^(2*m) ∧
    (4*d)^(2*m) ≤ (liftA d)^m := by
  have hcard : Nat.card (DFSSymbol d) = 2 * d + 1 := by
    rw [Nat.card_eq_fintype_card]
    unfold DFSSymbol
    simp [Fintype.card_option, Fintype.card_prod]
    omega
  refine ⟨hcard, ?_, ?_⟩
  · let f : {s : List (DFSSymbol d) // s.length ≤ 2 * m} → (Fin (2 * m) → Option (DFSSymbol d)) :=
      fun s i => s.val[i.val]?
    have hinj : Function.Injective f := by
      intro s₁ s₂ h
      apply Subtype.ext
      apply List.ext_getElem?
      intro i
      by_cases hi : i < 2 * m
      · exact congrFun h ⟨i, hi⟩
      · have h1 : s₁.val.length ≤ i := le_trans s₁.prop (Nat.le_of_not_lt hi)
        have h2 : s₂.val.length ≤ i := le_trans s₂.prop (Nat.le_of_not_lt hi)
        rw [List.getElem?_eq_none h1, List.getElem?_eq_none h2]
    have hle1 : Nat.card {s : List (DFSSymbol d) // s.length ≤ 2 * m} ≤
        Nat.card (Fin (2 * m) → Option (DFSSymbol d)) :=
      Nat.card_le_card_of_injective f hinj
    have hcod : Nat.card (Fin (2 * m) → Option (DFSSymbol d)) = (2 * d + 2) ^ (2 * m) := by
      rw [Nat.card_eq_fintype_card]
      unfold DFSSymbol
      simp [Fintype.card_pi, Fintype.card_option, Fintype.card_prod]
      congr 1
      omega
    have hle2 : (2 * d + 2) ^ (2 * m) ≤ (4 * d) ^ (2 * m) := by
      apply Nat.pow_le_pow_left
      omega
    exact le_trans (hcod ▸ hle1) hle2
  · rw [pow_mul]
    apply Nat.pow_le_pow_left
    unfold liftA
    calc
      (4 * d) ^ 2 = 16 * d ^ 2 := by
        rw [Nat.mul_pow]
      _ ≤ 64 * d ^ 2 := Nat.mul_le_mul_right (d ^ 2) (by decide)

end BuyAtBulk.EdgeOnlyGap
