import BuyAtBulk.EdgeOnlyGap.Items.CoefficientBits
import Mathlib.Data.Nat.Size

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 5, implicit: binary size of a reduced quotient of naturals is bounded
by the sizes of the unreduced numerator and denominator. -/
theorem proofC_bits_div (a b : ℕ) (hb : 0 < b) :
    coefficientBits ((a:ℚ) / b) ≤ 1 + a.size + b.size := by
  unfold coefficientBits
  have hq : ((a:ℚ) / b) = Rat.divInt a b := by
    rw [Rat.divInt_eq_div]; push_cast; rfl
  rw [hq]
  have hnum : (Rat.divInt a b).num.natAbs ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · have hd := Rat.num_dvd (a:ℤ) (b := (b:ℤ)) (by exact_mod_cast hb.ne')
      have := Int.natAbs_dvd_natAbs.mpr hd
      simpa using Nat.le_of_dvd ha this
  have hden : (Rat.divInt a b).den ≤ b := by
    have hd := Rat.den_dvd (a:ℤ) (b:ℤ)
    have : (Rat.divInt a b).den ∣ b := by exact_mod_cast hd
    exact Nat.le_of_dvd hb this
  have h1 := Nat.size_le_size hnum
  have h2 := Nat.size_le_size hden
  omega

theorem proofC_size_mul_ten (m : ℕ) : (10 * m).size ≤ m.size + 4 := by
  rw [Nat.size_le]
  have := Nat.lt_size_self m
  rw [pow_add]
  omega

end BuyAtBulk.EdgeOnlyGap
