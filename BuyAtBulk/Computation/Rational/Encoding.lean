import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Size
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Explicit unreduced binary rational representations. Arithmetic returns
integer numerator/denominator pairs, with a nonzero denominator. The bounds
below count bits of these actual representations, not of a real-number oracle. -/
namespace BuyAtBulk.Computation.Rational

structure Code where
  numerator : ℤ
  denominator : ℤ
  denominator_ne : denominator ≠ 0

namespace Code

def value (q : Code) : ℚ := (q.numerator : ℚ) / q.denominator

def ofRat (q : ℚ) : Code := ⟨q.num, q.den, by exact_mod_cast q.den_ne_zero⟩
def zero : Code := ⟨0, 1, by decide⟩
def add (q r : Code) : Code :=
  ⟨q.numerator * r.denominator + r.numerator * q.denominator,
    q.denominator * r.denominator, mul_ne_zero q.denominator_ne r.denominator_ne⟩
def mul (q r : Code) : Code :=
  ⟨q.numerator * r.numerator, q.denominator * r.denominator,
    mul_ne_zero q.denominator_ne r.denominator_ne⟩
def neg (q : Code) : Code := ⟨-q.numerator, q.denominator, q.denominator_ne⟩
def inv (q : Code) : Code :=
  if nonzero : q.numerator = 0 then zero else ⟨q.denominator, q.numerator, nonzero⟩
def div (q r : Code) : Code := q.mul r.inv

def bits (q : Code) : ℕ := q.numerator.natAbs.size + q.denominator.natAbs.size + 2

def Bounded (q : Code) (bound : ℕ) : Prop :=
  q.numerator.natAbs < 2 ^ bound ∧ q.denominator.natAbs < 2 ^ bound

@[simp] theorem ofRat_value (q : ℚ) : (ofRat q).value = q := q.num_div_den
@[simp] theorem zero_value : zero.value = 0 := by norm_num [zero, value]

@[simp] theorem add_value (q r : Code) : (q.add r).value = q.value + r.value := by
  have hq : (q.denominator : ℚ) ≠ 0 := by exact_mod_cast q.denominator_ne
  have hr : (r.denominator : ℚ) ≠ 0 := by exact_mod_cast r.denominator_ne
  simp only [add, value, Int.cast_add, Int.cast_mul]
  field_simp
  <;> ring

@[simp] theorem mul_value (q r : Code) : (q.mul r).value = q.value * r.value := by
  simp only [mul, value, Int.cast_mul]
  exact mul_div_mul_comm ..

@[simp] theorem neg_value (q : Code) : q.neg.value = -q.value := by
  simp only [neg, value, Int.cast_neg]
  exact neg_div ..

@[simp] theorem inv_value (q : Code) : q.inv.value = q.value⁻¹ := by
  by_cases hn : q.numerator = 0
  · simp [inv, hn, value, zero]
  · simp [inv, hn, value, inv_div]

@[simp] theorem div_value (q r : Code) : (q.div r).value = q.value / r.value := by
  simp [div, div_eq_mul_inv]

theorem bounded_bits {q : Code} {bound : ℕ} (h : q.Bounded bound) : q.bits ≤ 2 * bound + 2 := by
  have hn := Nat.size_le.mpr h.1
  have hd := Nat.size_le.mpr h.2
  dsimp [bits]
  omega

theorem bounded_of_bits (q : Code) : q.Bounded (q.bits + 1) := by
  constructor
  · exact (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) (by dsimp [bits]; omega))
  · exact (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) (by dsimp [bits]; omega))

private theorem product_bound {a b : ℤ} {k l : ℕ}
    (ha : a.natAbs < 2 ^ k) (hb : b.natAbs < 2 ^ l) :
    (a * b).natAbs < 2 ^ (k + l) := by
  rw [Int.natAbs_mul, pow_add]
  exact (Nat.mul_le_mul_left a.natAbs hb.le).trans_lt
    (mul_lt_mul_of_pos_right ha (by positivity))

theorem bounded_mono {q : Code} {k l : ℕ} (hq : q.Bounded k) (h : k ≤ l) : q.Bounded l :=
  ⟨hq.1.trans_le (Nat.pow_le_pow_right (by decide) h),
    hq.2.trans_le (Nat.pow_le_pow_right (by decide) h)⟩

theorem mul_bounded {q r : Code} {k l : ℕ}
    (hq : q.Bounded k) (hr : r.Bounded l) : (q.mul r).Bounded (k + l) :=
  ⟨product_bound hq.1 hr.1, product_bound hq.2 hr.2⟩

theorem add_bounded {q r : Code} {k l : ℕ}
    (hq : q.Bounded k) (hr : r.Bounded l) : (q.add r).Bounded (k + l + 1) := by
  have hn1 := product_bound hq.1 hr.2
  have hn2 := product_bound hr.1 hq.2
  have hd := product_bound hq.2 hr.2
  constructor
  · change (q.numerator * r.denominator + r.numerator * q.denominator).natAbs < _
    have triangle := Int.natAbs_add_le (q.numerator * r.denominator) (r.numerator * q.denominator)
    rw [Nat.add_comm l k] at hn2
    rw [pow_succ]
    omega
  · change (q.denominator * r.denominator).natAbs < _
    exact hd.trans_le (Nat.pow_le_pow_right (by decide) (by omega))

theorem neg_bounded {q : Code} {k : ℕ} (hq : q.Bounded k) : q.neg.Bounded k := by
  simpa only [Bounded, neg, Int.natAbs_neg] using hq

theorem inv_bounded {q : Code} {k : ℕ} (hq : q.Bounded k) (hk : 0 < k) : q.inv.Bounded k := by
  dsimp [inv]
  split_ifs
  · have hp : (1 : ℕ) < 2 ^ k := Nat.one_lt_pow (by omega) (by decide)
    exact ⟨by simpa [Bounded, zero] using (Nat.zero_lt_two_pow k), hp⟩
  · exact ⟨hq.2, hq.1⟩

theorem div_bounded {q r : Code} {k l : ℕ}
    (hq : q.Bounded k) (hr : r.Bounded l) (hl : 0 < l) : (q.div r).Bounded (k + l) :=
  mul_bounded hq (inv_bounded hr hl)

/-- Canonical rational normalization never enlarges either integer
component. This connects raw integer-pair bounds to Lean's normalized Rat. -/
theorem normalized_bits_le (q : Code) : (ofRat q.value).bits ≤ q.bits := by
  have numerator_dvd : q.value.num ∣ q.numerator := by
    simpa only [value, Rat.divInt_eq_div] using Rat.num_dvd q.numerator q.denominator_ne
  have denominator_dvd : (q.value.den : ℤ) ∣ q.denominator := by
    simpa only [value, Rat.divInt_eq_div] using Rat.den_dvd q.numerator q.denominator
  have numerator_le : q.value.num.natAbs ≤ q.numerator.natAbs := by
    by_cases zero : q.numerator = 0
    · simp [value, zero]
    · exact Nat.le_of_dvd (Int.natAbs_pos.mpr zero) (Int.natAbs_dvd_natAbs.mpr numerator_dvd)
  have denominator_le : q.value.den ≤ q.denominator.natAbs := by
    have divided := Int.natAbs_dvd_natAbs.mpr denominator_dvd
    simp only [Int.natAbs_natCast] at divided
    exact Nat.le_of_dvd (Int.natAbs_pos.mpr q.denominator_ne) divided
  simp only [bits, ofRat, Int.natAbs_natCast]
  have nbits := Nat.size_le_size numerator_le
  have dbits := Nat.size_le_size denominator_le
  omega

end Code
end BuyAtBulk.Computation.Rational
