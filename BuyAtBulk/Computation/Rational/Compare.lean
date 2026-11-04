import BuyAtBulk.Computation.Rational.Encoding

/-! Exact comparison of unreduced rational integer pairs, by cross-products.
It handles signed nonzero denominators and performs no rational normalization. -/
namespace BuyAtBulk.Computation.Rational.Code

def lessEqual (q r : Code) : Bool :=
  if 0 < q.denominator * r.denominator then
    decide (q.numerator * r.denominator ≤ r.numerator * q.denominator)
  else decide (r.numerator * q.denominator ≤ q.numerator * r.denominator)

private theorem difference (q r : Code) : q.value - r.value =
    ((q.numerator * r.denominator - r.numerator * q.denominator : ℤ) : ℚ) /
      ((q.denominator * r.denominator : ℤ) : ℚ) := by
  have hq : (q.denominator : ℚ) ≠ 0 := by exact_mod_cast q.denominator_ne
  have hr : (r.denominator : ℚ) ≠ 0 := by exact_mod_cast r.denominator_ne
  simp only [value, Int.cast_sub, Int.cast_mul]
  field_simp
  <;> ring

@[simp] theorem lessEqual_correct (q r : Code) : q.lessEqual r = true ↔ q.value ≤ r.value := by
  have nonzero : q.denominator * r.denominator ≠ 0 := mul_ne_zero q.denominator_ne r.denominator_ne
  by_cases positive : 0 < q.denominator * r.denominator
  · have positiveQ : (0 : ℚ) < ((q.denominator * r.denominator : ℤ) : ℚ) := by exact_mod_cast positive
    simp only [lessEqual, if_pos positive, decide_eq_true_eq]
    conv_rhs => rw [← sub_nonpos, difference]
    rw [div_nonpos_iff]
    have cross : ((q.numerator * r.denominator - r.numerator * q.denominator : ℤ) : ℚ) ≤ 0 ↔
        q.numerator * r.denominator ≤ r.numerator * q.denominator := by
      exact_mod_cast (sub_nonpos : q.numerator * r.denominator - r.numerator * q.denominator ≤ 0 ↔ _)
    simp only [positiveQ.le, positiveQ.not_ge, and_true, and_false, or_false, false_or, cross]
  · have negative : q.denominator * r.denominator < 0 := lt_of_le_of_ne (le_of_not_gt positive) nonzero
    have negativeQ : (((q.denominator * r.denominator : ℤ) : ℚ)) < 0 := by exact_mod_cast negative
    simp only [lessEqual, if_neg positive, decide_eq_true_eq]
    conv_rhs => rw [← sub_nonpos, difference]
    rw [div_nonpos_iff]
    have cross : (0 : ℚ) ≤ ((q.numerator * r.denominator - r.numerator * q.denominator : ℤ) : ℚ) ↔
        r.numerator * q.denominator ≤ q.numerator * r.denominator := by
      exact_mod_cast (sub_nonneg : 0 ≤ q.numerator * r.denominator - r.numerator * q.denominator ↔ _)
    simp only [negativeQ.le, negativeQ.not_ge, and_true, and_false, false_or, or_false, cross]

/-- Every transient cross-product used by comparison has magnitude bit length
at most the sum of the two input exponent budgets. -/
theorem comparison_integer_bits (q r : Code) (k l : ℕ)
    (hq : q.Bounded k) (hr : r.Bounded l) :
    (q.numerator * r.denominator).natAbs.size ≤ k + l ∧
    (r.numerator * q.denominator).natAbs.size ≤ k + l ∧
    (q.denominator * r.denominator).natAbs.size ≤ k + l := by
  have product : ∀ (a b : ℤ) (j m : ℕ), a.natAbs < 2 ^ j → b.natAbs < 2 ^ m →
      (a * b).natAbs.size ≤ j + m := by
    intro a b j m ha hb
    apply Nat.size_le.mpr
    rw [Int.natAbs_mul, pow_add]
    exact (Nat.mul_le_mul_left a.natAbs hb.le).trans_lt
      (mul_lt_mul_of_pos_right ha (by positivity))
  exact ⟨product _ _ _ _ hq.1 hr.2,
    by simpa only [Nat.add_comm l k] using product _ _ _ _ hr.1 hq.2,
    product _ _ _ _ hq.2 hr.2⟩

end BuyAtBulk.Computation.Rational.Code
