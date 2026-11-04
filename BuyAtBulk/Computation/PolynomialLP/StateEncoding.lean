import BuyAtBulk.Computation.PolynomialLP.StateInvariant
import BuyAtBulk.Computation.PolynomialLP.SquareRootBits

/-! Finite binary encodings of rounded states. Magnitude and denominator
bounds are proved about the returned rational values, rather than assumed as
an execution certificate. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace BuyAtBulk.PolynomialLP
open Computation.Rational

theorem rational_bits_of_denominator (q : ℚ) (L p : ℕ)
    (magnitude : |q| ≤ (2 : ℚ) ^ L) (denominator : q.den ≤ 2 ^ p) :
    (Code.ofRat q).bits ≤ 2 * (L + p + 1) + 2 := by
  have den_pos : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have den_cast : (q.den : ℚ) ≤ (2 : ℚ) ^ p := by exact_mod_cast denominator
  have num_eq : (q.num.natAbs : ℚ) = |q| * q.den := by
    have absolute : (q.num.natAbs : ℚ) = |(q.num : ℚ)| := by
      have cast := congrArg (fun z : ℤ => (z : ℚ)) (Int.natCast_natAbs q.num)
      simpa only [Int.cast_natCast, Int.cast_abs] using cast
    rw [absolute]
    conv_rhs => lhs; rw [← q.num_div_den]
    rw [abs_div, abs_of_pos den_pos]
    exact (div_mul_cancel₀ _ (ne_of_gt den_pos)).symm
  have numerator : q.num.natAbs ≤ 2 ^ (L + p) := by
    have bound : (q.num.natAbs : ℚ) ≤ (2 : ℚ) ^ (L + p) := by
      rw [num_eq, pow_add]
      exact mul_le_mul magnitude den_cast (by positivity) (by positivity)
    exact_mod_cast bound
  apply Code.bounded_bits
  constructor
  · exact numerator.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))
  · change q.den < 2 ^ (L + p + 1)
    exact denominator.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))

theorem denominator_of_code (code : Code) : code.value.den ≤ code.denominator.natAbs := by
  have divided : (code.value.den : ℤ) ∣ code.denominator := by
    simpa only [Code.value, Rat.divInt_eq_div] using
      Rat.den_dvd code.numerator code.denominator
  have dividedNat := Int.natAbs_dvd_natAbs.mpr divided
  simp only [Int.natAbs_natCast] at dividedNat
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr code.denominator_ne) dividedNat

theorem dyadic_denominator (q : ℚ) (p : ℕ) : (dyadicCode q p).value.den ≤ 2 ^ p := by
  have bound := denominator_of_code (dyadicCode q p)
  simpa [dyadicCode, Int.natAbs_pow] using bound

theorem dyadic_plus_grid_denominator (q : ℚ) (p : ℕ) (shift : ℤ) :
    ((dyadicCode q p).value + (shift : ℚ) / (2 : ℚ) ^ p).den ≤ 2 ^ p := by
  let code : Code := ⟨dyadicNumerator q p + shift, (2 : ℤ) ^ p,
    pow_ne_zero _ (by decide)⟩
  have decoded : code.value = (dyadicCode q p).value + (shift : ℚ) / (2 : ℚ) ^ p := by
    simp only [code, Code.value, dyadicCode, Int.cast_add, Int.cast_pow, Int.cast_ofNat]
    ring
  rw [← decoded]
  have bound := denominator_of_code code
  simpa [code, Int.natAbs_pow] using bound

variable {n : ℕ}

theorem roundedStep_center_denominator (state : Ellipsoid n) (direction : Vector ℚ n)
    (p : ℕ) (i : Fin n) :
    ((state.roundedStep direction p).center[i.val]).den ≤ 2 ^ p := by
  simpa only [Ellipsoid.roundedStep, Vector.getElem_map] using
    dyadic_denominator ((state.rawCenter direction)[i.val]) p

theorem roundedStep_shape_denominator (state : Ellipsoid n) (direction : Vector ℚ n)
    (p : ℕ) (i j : Fin n) :
    ((state.roundedStep direction p).shape[i.val][j.val]).den ≤ 2 ^ p := by
  simp only [Ellipsoid.roundedStep, Vector.getElem_ofFn]
  by_cases same : i = j
  · subst j
    simp only [ite_true]
    exact dyadic_plus_grid_denominator _ p (n : ℤ)
  · simp only [same, if_false, add_zero]
    exact dyadic_denominator _ _

theorem stateMagnitude_binary (n age : ℕ) : stateMagnitude n age ≤ 2 ^ (n + 1 + 4 * age) := by
  unfold stateMagnitude
  have power : 16 ^ age = (2 : ℕ) ^ (4 * age) := by
    rw [pow_mul]; norm_num
  rw [power, pow_add]
  exact Nat.mul_le_mul_right _ (Nat.lt_two_pow_self.le)

noncomputable section

theorem invariant_center_magnitude (state : Ellipsoid n) (age : ℕ)
    (valid : EllipsoidInvariant state age) (i : Fin n) :
    |state.center[i.val]| ≤ (2 : ℚ) ^ (n + 1 + 4 * age) := by
  have bound := (valid.center i).trans
    (show (stateMagnitude n age : ℝ) ≤ (2 : ℝ) ^ (n + 1 + 4 * age) by
      exact_mod_cast stateMagnitude_binary n age)
  change |(state.center[i.val] : ℝ)| ≤ _ at bound
  exact_mod_cast bound

theorem invariant_shape_magnitude (state : Ellipsoid n) (age : ℕ)
    (valid : EllipsoidInvariant state age) (i j : Fin n) :
    |state.shape[i.val][j.val]| ≤ (2 : ℚ) ^ (n + 1 + 4 * age) := by
  have bound := (matrix_entries_upper _ valid.positive (stateMagnitude n age : ℝ)
    (by positivity) (fun x => (valid.forms x).2) i j).trans
    (show (stateMagnitude n age : ℝ) ≤ (2 : ℝ) ^ (n + 1 + 4 * age) by
      exact_mod_cast stateMagnitude_binary n age)
  change |(state.shape[i.val][j.val] : ℝ)| ≤ _ at bound
  exact_mod_cast bound

end
end BuyAtBulk.PolynomialLP
