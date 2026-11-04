import BuyAtBulk.Computation.Rational.Encoding
import Mathlib.Tactic.NormNum

/-! Exact positive rational gaps determined by binary encoding bounds.
These precision lemmas are independent of any proposed LP algorithm. -/
namespace BuyAtBulk.PolynomialLP
open Computation.Rational

theorem positive_rational_lower (q : ℚ) (positive : 0 < q) (D : ℕ) (denominator : q.den ≤ D) :
    1 / (D : ℚ) ≤ q := by
  have den_pos : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have D_pos : (0 : ℚ) < D := by exact_mod_cast q.den_pos.trans_le denominator
  have numerator_pos : (0 : ℤ) < q.num := Rat.num_pos.mpr positive
  have numerator_one : (1 : ℚ) ≤ q.num := by exact_mod_cast (show (1 : ℤ) ≤ q.num by omega)
  have representation : (q.num : ℚ) = q * q.den := (div_eq_iff (ne_of_gt den_pos)).mp q.num_div_den
  apply (div_le_iff₀ D_pos).mpr
  have den_le : (q.den : ℚ) ≤ D := by exact_mod_cast denominator
  nlinarith [mul_le_mul_of_nonneg_left den_le positive.le]

theorem rational_gap (q r : ℚ) (less : q < r) (D : ℕ)
    (q_den : q.den ≤ D) (r_den : r.den ≤ D) :
    1 / ((D : ℚ) * D) ≤ r - q := by
  have qpos : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have rpos : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
  have Dpos : (0 : ℚ) < D := by exact_mod_cast q.den_pos.trans_le q_den
  have qrep : (q.num : ℚ) = q * q.den := (div_eq_iff (ne_of_gt qpos)).mp q.num_div_den
  have rrep : (r.num : ℚ) = r * r.den := (div_eq_iff (ne_of_gt rpos)).mp r.num_div_den
  let cross : ℤ := r.num * (q.den : ℤ) - q.num * (r.den : ℤ)
  have cross_value : (cross : ℚ) = (r - q) * ((q.den : ℚ) * r.den) := by
    dsimp [cross]
    push_cast
    rw [qrep, rrep]
    ring
  have cross_pos : (0 : ℤ) < cross := by
    have cast_pos : (0 : ℚ) < cross := by rw [cross_value]; positivity
    exact_mod_cast cast_pos
  have cross_one : (1 : ℚ) ≤ cross := by exact_mod_cast (show (1 : ℤ) ≤ cross by omega)
  have denominator_le : (q.den : ℚ) * r.den ≤ (D : ℚ) * D :=
    mul_le_mul (by exact_mod_cast q_den) (by exact_mod_cast r_den) rpos.le Dpos.le
  apply (div_le_iff₀ (mul_pos Dpos Dpos)).mpr
  rw [cross_value] at cross_one
  exact cross_one.trans (mul_le_mul_of_nonneg_left denominator_le (sub_pos.mpr less).le)

theorem denominator_le_of_bits (q : ℚ) (L : ℕ) (bits : (Code.ofRat q).bits ≤ L) :
    q.den ≤ 2 ^ (L + 1) := by
  have bound := (Code.ofRat q).bounded_of_bits.2
  simp only [Code.ofRat, Int.natAbs_natCast] at bound
  change q.den < 2 ^ ((Code.ofRat q).bits + 1) at bound
  exact bound.le.trans (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right bits 1))

theorem positive_encoding_lower (q : ℚ) (L : ℕ) (positive : 0 < q)
    (bits : (Code.ofRat q).bits ≤ L) : 1 / (2 : ℚ) ^ (L + 1) ≤ q := by
  have bound := positive_rational_lower q positive (2 ^ (L + 1)) (denominator_le_of_bits q L bits)
  exact_mod_cast bound

theorem encoding_gap (q r : ℚ) (L : ℕ) (less : q < r)
    (q_bits : (Code.ofRat q).bits ≤ L) (r_bits : (Code.ofRat r).bits ≤ L) :
    1 / (2 : ℚ) ^ (2 * (L + 1)) ≤ r - q := by
  have bound := rational_gap q r less (2 ^ (L + 1))
    (denominator_le_of_bits q L q_bits) (denominator_le_of_bits r L r_bits)
  push_cast at bound
  simpa only [two_mul, pow_add] using bound

end BuyAtBulk.PolynomialLP
