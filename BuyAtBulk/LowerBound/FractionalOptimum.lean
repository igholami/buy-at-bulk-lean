import BuyAtBulk.LowerBound.Construction
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace BuyAtBulk.LowerBound
open scoped BigOperators

/-- The exact fractional optimum of the source covering construction. -/
theorem fractional_optimum (k : ℕ) (hk : 1 ≤ k) :
    (∀ x : Ground k → ℝ, FractionalCover k x →
      2 ≤ ∑ j, x j) ∧
    ∃ x : Ground k → ℝ, FractionalCover k x ∧ ∑ j, x j = 2 := by
  classical
  have hk0 : k ≠ 0 := by omega
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  constructor
  · intro x hx
    have hbound : k ≤ (Finset.univ : Finset (Ground k)).card := by
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨A, _, hA⟩ := Finset.exists_subset_card_eq hbound
    have hAc : Aᶜ.card = k := by
      simp only [Finset.card_compl, Fintype.card_fin, hA]
      omega
    have ha := hx.2 A hA
    have hb := hx.2 Aᶜ hAc
    have heq := Finset.sum_add_sum_compl A x
    linarith
  · refine ⟨fun _ => 1 / (k : ℝ), ⟨?_, ?_⟩, ?_⟩
    · intro j
      constructor
      · positivity
      · exact (div_le_one hkr).mpr (by exact_mod_cast hk)
    · intro A hA
      simp only [Finset.sum_const, nsmul_eq_mul, hA]
      field_simp [ne_of_gt hkr]
      norm_num

    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
      field_simp [ne_of_gt hkr]


end BuyAtBulk.LowerBound
