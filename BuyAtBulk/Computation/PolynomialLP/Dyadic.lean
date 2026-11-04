import BuyAtBulk.Computation.Rational.Encoding
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! Actual dyadic rounding by integer multiplication and Euclidean division.
The program returns an integer-pair code with denominator exactly 2^precision;
its error and stored code size are proved without a rounding oracle. -/
namespace BuyAtBulk.PolynomialLP
open Computation.Rational

def dyadicNumerator (q : ℚ) (precision : ℕ) : ℤ :=
  (q.num * (2 : ℤ) ^ precision) / (q.den : ℤ)

def dyadicCode (q : ℚ) (precision : ℕ) : Code :=
  ⟨dyadicNumerator q precision, (2 : ℤ) ^ precision, pow_ne_zero _ (by decide)⟩

theorem dyadicNumerator_floor (q : ℚ) (precision : ℕ) :
    dyadicNumerator q precision = ⌊q * (2 : ℚ) ^ precision⌋ := by
  unfold dyadicNumerator
  rw [← Rat.floor_intCast_div_natCast]
  congr 1
  push_cast
  calc
    (q.num : ℚ) * 2 ^ precision / q.den = ((q.num : ℚ) / q.den) * 2 ^ precision := by ring
    _ = _ := by rw [q.num_div_den]

theorem dyadicCode_value (q : ℚ) (precision : ℕ) :
    (dyadicCode q precision).value =
      (⌊q * (2 : ℚ) ^ precision⌋ : ℚ) / (2 : ℚ) ^ precision := by
  simp only [dyadicCode, Code.value, dyadicNumerator_floor, Int.cast_pow, Int.cast_ofNat]

/-- Downward rounding has one dyadic unit of error, for arbitrary signed q. -/
theorem dyadic_error (q : ℚ) (precision : ℕ) :
    (dyadicCode q precision).value ≤ q ∧
      q < (dyadicCode q precision).value + 1 / (2 : ℚ) ^ precision := by
  rw [dyadicCode_value]
  have positive : (0 : ℚ) < 2 ^ precision := by positivity
  constructor
  · exact (div_le_iff₀ positive).mpr (Int.floor_le _)
  · have bound := Int.lt_floor_add_one (q * (2 : ℚ) ^ precision)
    have result := (lt_div_iff₀ positive).mpr bound
    simpa only [add_div] using result

theorem dyadic_abs_error (q : ℚ) (precision : ℕ) :
    |(dyadicCode q precision).value - q| < 1 / (2 : ℚ) ^ precision := by
  obtain ⟨lower, upper⟩ := dyadic_error q precision
  rw [abs_of_nonpos (sub_nonpos.mpr lower)]
  linarith

/-- Even an unreduced returned pair has polynomial bit size in the magnitude
exponent and the requested precision. -/
theorem dyadic_bits (q : ℚ) (precision L : ℕ) (magnitude : |q| ≤ (2 : ℚ) ^ L) :
    (dyadicCode q precision).bits ≤ 2 * (L + precision + 2) + 2 := by
  have scale_pos : (0 : ℚ) < 2 ^ precision := by positivity
  have scaled_abs : |q * (2 : ℚ) ^ precision| ≤ (2 : ℚ) ^ (L + precision) := by
    rw [abs_mul, abs_of_pos scale_pos, pow_add]
    exact mul_le_mul_of_nonneg_right magnitude scale_pos.le
  have floor_lower := Int.floor_le (q * (2 : ℚ) ^ precision)
  have floor_upper := Int.lt_floor_add_one (q * (2 : ℚ) ^ precision)
  have numerator_abs : |(dyadicNumerator q precision : ℚ)| < (2 : ℚ) ^ (L + precision) + 1 := by
    rw [dyadicNumerator_floor, abs_lt]
    obtain ⟨scaled_lower, scaled_upper⟩ := abs_le.mp scaled_abs
    constructor <;> linarith
  have power_pos : (0 : ℚ) < 2 ^ (L + precision) := by positivity
  have numerator_bound : (dyadicNumerator q precision).natAbs < 2 ^ (L + precision + 2) := by
    have cast_abs : ((dyadicNumerator q precision).natAbs : ℚ) = |(dyadicNumerator q precision : ℚ)| := by
      have cast := congrArg (fun z : ℤ => (z : ℚ)) (Int.natCast_natAbs (dyadicNumerator q precision))
      simpa only [Int.cast_natCast, Int.cast_abs] using cast
    have rational : ((dyadicNumerator q precision).natAbs : ℚ) < (2 : ℚ) ^ (L + precision + 2) := by
      rw [cast_abs, pow_add]
      norm_num
      have one : (1 : ℚ) ≤ 2 ^ (L + precision) := one_le_pow₀ (by norm_num)
      nlinarith
    exact_mod_cast rational
  have denominator_bound : ((2 : ℤ) ^ precision).natAbs < 2 ^ (L + precision + 2) := by
    rw [Int.natAbs_pow]
    norm_num
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  exact Code.bounded_bits ⟨numerator_bound, denominator_bound⟩

inductive DyadicOperation where
  | read | power | mul | div | pair | write
  deriving DecidableEq, Repr

structure DyadicEvent where
  operation : DyadicOperation
  operands : List ℤ
  deriving Repr

/-- The closed primitive schedule includes the actual integer dividend and
quotient used to round, with no user-supplied cost field. -/
def dyadicTrace (q : ℚ) (precision : ℕ) : List DyadicEvent :=
  let denominator : ℤ := 2 ^ precision
  let dividend := q.num * denominator
  let numerator := dividend / (q.den : ℤ)
  [⟨.read, [q.num, q.den]⟩,
   ⟨.power, [2, precision, denominator]⟩,
   ⟨.mul, [q.num, denominator, dividend]⟩,
   ⟨.div, [dividend, q.den, numerator]⟩,
   ⟨.pair, [numerator, denominator]⟩,
   ⟨.write, [numerator, denominator]⟩]

theorem dyadicTrace_length (q : ℚ) (precision : ℕ) : (dyadicTrace q precision).length = 6 := rfl

end BuyAtBulk.PolynomialLP
