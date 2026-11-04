import BuyAtBulk.Computation.PolynomialLP.Dyadic
import BuyAtBulk.Computation.Runtime.OriginalDecode
import BuyAtBulk.Computation.Runtime.Numerical

/-! Dyadic rounding with an explicit doubling loop. The integer dividend,
floor quotient and raw pair passed to rational normalization are all charged. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace BuyAtBulk.PolynomialLP.Trace
open BuyAtBulk.Computation BuyAtBulk.Computation.Runtime
open Rational

def dyadic (q : ℚ) (precision : ℕ) : Traced ℚ :=
  let power := powerTwo precision
  let denominator : ℤ := power.value
  let dividend := q.num * denominator
  let numerator := dividend / (q.den : ℤ)
  have nonzero : denominator ≠ 0 := by simp [denominator, power]
  let pair : Code := ⟨numerator, denominator, nonzero⟩
  let decoded := Original.decodeRat pair
  ⟨decoded.value, power.events ++
    [⟨.read, [q.num.natAbs.size+1, q.den.size]⟩,
     ⟨.ratCast, [power.value.size, denominator.natAbs.size+1]⟩,
     ⟨.intMul, [q.num.natAbs.size+1, denominator.natAbs.size+1, dividend.natAbs.size+1]⟩,
     ⟨.intDiv, [dividend.natAbs.size+1, q.den.size, numerator.natAbs.size+1]⟩,
     ⟨.write, [pair.bits]⟩] ++ decoded.events⟩

theorem dyadic_value (q : ℚ) (precision : ℕ) :
    (dyadic q precision).value = (dyadicCode q precision).value := by
  simp only [dyadic, Original.decodeRat_value, powerTwo_value, dyadicCode, dyadicNumerator, Int.natCast_pow, Nat.cast_ofNat]


theorem dyadic_count (q : ℚ) (precision : ℕ) :
    (dyadic q precision).events.length = 2*precision+13 := by
  simp only [dyadic, List.length_append, List.length_cons, List.length_nil,
    powerTwo_count, Original.decodeRat_count]

end BuyAtBulk.PolynomialLP.Trace
