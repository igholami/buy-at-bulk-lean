import BuyAtBulk.Computation.Runtime.Primitive
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import BuyAtBulk.Computation.PolynomialLP.RationalGap

/-! Rational square-root bracketing by a fixed binary schedule. All data are
rational; neither real square root nor a supplied approximation is evaluated. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP
open Computation.Runtime

def midpoint (lower upper : ℚ) : Traced ℚ := do
  let sum ← ratAdd lower upper
  ratDiv sum 2

@[simp] theorem midpoint_value (lower upper : ℚ) :
    (midpoint lower upper).value = (lower + upper) / 2 := rfl
@[simp] theorem midpoint_count (lower upper : ℚ) :
    (midpoint lower upper).events.length = 4 := rfl

def sqrtBisect (q : ℚ) : ℕ → ℚ → ℚ → Traced (ℚ × ℚ)
  | 0, lower, upper => Traced.pure (lower, upper)
  | fuel + 1, lower, upper => do
      let _ ← emit .recurse [fuel.size] ()
      let middle ← midpoint lower upper
      let square ← ratMul middle middle
      let test ← ratLe square q
      let test ← branch test
      if test then sqrtBisect q fuel middle upper else sqrtBisect q fuel lower middle

theorem sqrtBisect_succ (q : ℚ) (fuel : ℕ) (lower upper : ℚ) :
    (sqrtBisect q (fuel + 1) lower upper).value =
      if ((lower + upper) / 2) ^ 2 ≤ q then
        (sqrtBisect q fuel ((lower + upper) / 2) upper).value
      else (sqrtBisect q fuel lower ((lower + upper) / 2)).value := by
  simp only [sqrtBisect, Traced.bind_value, emit_value, midpoint_value, ratMul_value,
    ratLe, branch, Traced.ite_value, decide_eq_true_eq, pow_two]

theorem sqrtBisect_count (q : ℚ) (fuel : ℕ) (lower upper : ℚ) :
    (sqrtBisect q fuel lower upper).events.length = 9 * fuel := by
  induction fuel generalizing lower upper with
  | zero => rfl
  | succ fuel ih =>
    simp only [sqrtBisect, Traced.bind_events, Traced.bind_value, List.length_append,
      emit_length, midpoint_count, ratMul_length, ratLe, branch, emit_value]
    simp only [Traced.ite_events]
    split_ifs <;> simp only [ih, emit_length] <;> omega

def Brackets (q lower upper : ℚ) : Prop :=
  0 ≤ lower ∧ lower ≤ upper ∧ lower ^ 2 ≤ q ∧ q ≤ upper ^ 2

theorem sqrtBisect_brackets (q : ℚ) (fuel : ℕ) (lower upper : ℚ) (valid : Brackets q lower upper) :
    Brackets q (sqrtBisect q fuel lower upper).value.1 (sqrtBisect q fuel lower upper).value.2 := by
  induction fuel generalizing lower upper with
  | zero => exact valid
  | succ fuel ih =>
    rw [sqrtBisect_succ]
    obtain ⟨lower_nonneg, ordered, lower_square, upper_square⟩ := valid
    split_ifs with test
    · apply ih
      refine ⟨by linarith, by linarith, test, upper_square⟩
    · apply ih
      exact ⟨lower_nonneg, by linarith, lower_square, (not_le.mp test).le⟩

theorem sqrtBisect_nested (q : ℚ) (fuel : ℕ) (lower upper : ℚ) (ordered : lower ≤ upper) :
    lower ≤ (sqrtBisect q fuel lower upper).value.1 ∧
      (sqrtBisect q fuel lower upper).value.2 ≤ upper := by
  induction fuel generalizing lower upper with
  | zero => exact ⟨le_rfl, le_rfl⟩
  | succ fuel ih =>
    rw [sqrtBisect_succ]
    split_ifs
    · obtain ⟨left, right⟩ := ih ((lower + upper) / 2) upper (by linarith)
      exact ⟨by linarith, right⟩
    · obtain ⟨left, right⟩ := ih lower ((lower + upper) / 2) (by linarith)
      exact ⟨left, by linarith⟩

theorem sqrtBisect_width (q : ℚ) (fuel : ℕ) (lower upper : ℚ) :
    (sqrtBisect q fuel lower upper).value.2 - (sqrtBisect q fuel lower upper).value.1 =
      (upper - lower) / (2 : ℚ) ^ fuel := by
  induction fuel generalizing lower upper with
  | zero => simp [sqrtBisect, Traced.pure]
  | succ fuel ih =>
    rw [sqrtBisect_succ]
    split_ifs <;> rw [ih, pow_succ] <;> ring

def sqrtBracket (q : ℚ) (precision : ℕ) : Traced (ℚ × ℚ) := do
  let upper ← ratAdd q 1
  sqrtBisect q precision 0 upper

/-- An actual rational interval containing the nonnegative square root, with
exact exponentially decreasing width and a linear primitive schedule. -/
theorem sqrtBracket_contract (q : ℚ) (nonneg : 0 ≤ q) (precision : ℕ) :
    Brackets q (sqrtBracket q precision).value.1 (sqrtBracket q precision).value.2 ∧
    0 ≤ (sqrtBracket q precision).value.1 ∧
    (sqrtBracket q precision).value.2 ≤ q + 1 ∧
    (sqrtBracket q precision).value.2 - (sqrtBracket q precision).value.1 = (q + 1) / (2 : ℚ) ^ precision ∧
    (sqrtBracket q precision).events.length = 9 * precision + 2 := by
  have valid : Brackets q 0 (q + 1) := by
    refine ⟨le_rfl, by linarith, by simpa using nonneg, ?_⟩
    nlinarith [sq_nonneg q]
  have brackets := sqrtBisect_brackets q precision 0 (q + 1) valid
  have nested := sqrtBisect_nested q precision 0 (q + 1) (by linarith)
  refine ⟨brackets, nested.1, nested.2, by simpa only [sqrtBracket, Traced.bind_value, ratAdd_value, sub_zero] using sqrtBisect_width q precision 0 (q + 1), ?_⟩
  simp only [sqrtBracket, Traced.bind_events, Traced.bind_value, ratAdd_value,
    List.length_append, ratAdd_length, sqrtBisect_count]
  omega

theorem sqrtBracket_square_error (q : ℚ) (nonneg : 0 ≤ q) (precision : ℕ) :
    (sqrtBracket q precision).value.2 ^ 2 - q ≤ 2 * (q + 1) ^ 2 / (2 : ℚ) ^ precision := by
  obtain ⟨bracket, _, upper_bound, width, _⟩ := sqrtBracket_contract q nonneg precision
  obtain ⟨lower_nonneg, ordered, lower_square, upper_square⟩ := bracket
  have positive : (0 : ℚ) < 2 ^ precision := by positivity
  have square_difference := mul_le_mul_of_nonneg_left
    (show (sqrtBracket q precision).value.2 + (sqrtBracket q precision).value.1 ≤ 2 * (q + 1) by linarith)
    (sub_nonneg.mpr ordered)
  calc
    _ ≤ (sqrtBracket q precision).value.2 ^ 2 - (sqrtBracket q precision).value.1 ^ 2 := by linarith
    _ = ((sqrtBracket q precision).value.2 - (sqrtBracket q precision).value.1) *
        ((sqrtBracket q precision).value.2 + (sqrtBracket q precision).value.1) := by ring
    _ ≤ _ := square_difference
    _ = _ := by rw [width]; ring

theorem sqrtBracket_relative (q : ℚ) (L precision : ℕ)
    (lower : 1 / (2 : ℚ) ^ L ≤ q) (upper : q ≤ (2 : ℚ) ^ L) :
    (sqrtBracket q (3 * L + precision + 3)).value.2 ^ 2 ≤ q + q / (2 : ℚ) ^ precision := by
  let a : ℚ := 2 ^ L
  let b : ℚ := 2 ^ precision
  have a_pos : 0 < a := by dsimp [a]; positivity
  have a_one : 1 ≤ a := by dsimp [a]; exact one_le_pow₀ (by norm_num)
  have b_pos : 0 < b := by dsimp [b]; positivity
  have q_pos : 0 < q := lt_of_lt_of_le (by positivity : 0 < 1 / a) lower
  have q_a : 1 ≤ q * a := (div_le_iff₀ a_pos).mp lower
  have cube_bound : a ^ 2 ≤ q * a ^ 3 := by
    have multiplied := mul_le_mul_of_nonneg_right q_a (sq_nonneg a)
    nlinarith
  have sum_bound : (q + 1) ^ 2 ≤ 4 * a ^ 2 := by
    have difference : 0 ≤ (a + 1) ^ 2 - (q + 1) ^ 2 := by nlinarith [sq_nonneg (a - q)]
    nlinarith [sq_nonneg (a - 1)]
  have powers : (2 : ℚ) ^ (3 * L + precision + 3) = 8 * a ^ 3 * b := by
    dsimp [a, b]
    rw [show 3 * L + precision + 3 = L + L + L + precision + 3 by omega]
    simp only [pow_add]
    norm_num
    ring
  have error := sqrtBracket_square_error q q_pos.le (3 * L + precision + 3)
  rw [powers] at error
  have relative : 2 * (q + 1) ^ 2 / (8 * a ^ 3 * b) ≤ q / b := by
    apply (div_le_div_iff₀ (by positivity : 0 < 8 * a ^ 3 * b) b_pos).mpr
    have bound : 2 * (q + 1) ^ 2 ≤ 8 * q * a ^ 3 := by nlinarith
    have multiplied := mul_le_mul_of_nonneg_right bound b_pos.le
    nlinarith
  exact (by linarith [error.trans relative])

theorem rational_abs_binary_bound (q : ℚ) :
    |q| ≤ (2 : ℚ) ^ ((Computation.Rational.Code.ofRat q).bits + 1) := by
  have numerator := (Computation.Rational.Code.ofRat q).bounded_of_bits.1
  have numerator_cast : (q.num.natAbs : ℚ) ≤
      (2 : ℚ) ^ ((Computation.Rational.Code.ofRat q).bits + 1) := by exact_mod_cast numerator.le
  have absolute_num : (q.num.natAbs : ℚ) = |(q.num : ℚ)| := by
    have cast := congrArg (fun z : ℤ => (z : ℚ)) (Int.natCast_natAbs q.num)
    simpa only [Int.cast_natCast, Int.cast_abs] using cast
  rw [absolute_num] at numerator_cast
  have den_pos : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have den_one : (1 : ℚ) ≤ q.den := by exact_mod_cast q.den_pos
  conv_lhs => rw [← q.num_div_den, abs_div, abs_of_pos den_pos]
  apply (div_le_iff₀ den_pos).mpr
  exact numerator_cast.trans (le_mul_of_one_le_right (by positivity) den_one)

def relativeSqrt (q : ℚ) (precision : ℕ) : Traced (ℚ × ℚ) :=
  sqrtBracket q (3 * ((Computation.Rational.Code.ofRat q).bits + 1) + precision + 3)

/-- The precision schedule is determined from the actual normalized input
encoding. The returned upper endpoint gives a relative squared approximation. -/
theorem relativeSqrt_contract (q : ℚ) (positive : 0 < q) (precision : ℕ) :
    let upper := (relativeSqrt q precision).value.2
    0 < upper ∧ q ≤ upper ^ 2 ∧ upper ^ 2 ≤ q + q / (2 : ℚ) ^ precision ∧
      (relativeSqrt q precision).events.length =
        9 * (3 * ((Computation.Rational.Code.ofRat q).bits + 1) + precision + 3) + 2 := by
  dsimp only
  have lower := positive_encoding_lower q _ positive le_rfl
  have upper := (le_abs_self q).trans (rational_abs_binary_bound q)
  have relative := sqrtBracket_relative q _ precision lower upper
  obtain ⟨bracket, _, _, _, count⟩ := sqrtBracket_contract q positive.le
    (3 * ((Computation.Rational.Code.ofRat q).bits + 1) + precision + 3)
  refine ⟨?_, bracket.2.2.2, relative, count⟩
  change 0 < (sqrtBracket q (3 * ((Computation.Rational.Code.ofRat q).bits + 1) + precision + 3)).value.2
  have nonneg := bracket.1.trans bracket.2.1
  nlinarith [bracket.2.2.2]

end BuyAtBulk.PolynomialLP
