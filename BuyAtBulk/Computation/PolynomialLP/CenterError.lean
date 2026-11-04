import BuyAtBulk.Computation.PolynomialLP.DualBall
import BuyAtBulk.Computation.PolynomialLP.Dyadic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Lemmas

/-! Coordinate rounding is small in every support direction when the stored
shape has an explicit lower quadratic envelope. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.PolynomialLP
open scoped Matrix BigOperators
variable {n : ℕ}

def normSquared (x : Fin n → ℝ) : ℝ := ∑ i, x i ^ 2

theorem normSquared_nonneg (x : Fin n → ℝ) : 0 ≤ normSquared x := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem coordinateError_support (Q : Matrix (Fin n) (Fin n) ℝ) (lower delta tau : ℝ)
    (envelope : ∀ x, lower * normSquared x ≤ qform Q x)
    (tau_nonneg : 0 ≤ tau) (precision : (n : ℝ) * tau ^ 2 ≤ delta ^ 2 * lower)
    (error : Fin n → ℝ) (coordinates : ∀ i, |error i| ≤ tau) :
    ∀ a, (a ⬝ᵥ error) ^ 2 ≤ delta ^ 2 * qform Q a := by
  intro a
  have sum_error : normSquared error ≤ (n : ℝ) * tau ^ 2 := by
    have pointwise : ∀ i : Fin n, error i ^ 2 ≤ tau ^ 2 := by
      intro i
      have absolute := coordinates i
      have square := sq_le_sq₀ (abs_nonneg (error i)) tau_nonneg |>.mpr absolute
      simpa only [sq_abs] using square
    calc
      _ ≤ ∑ _ : Fin n, tau ^ 2 := Finset.sum_le_sum fun i _ => pointwise i
      _ = _ := by simp
  have cauchy : (a ⬝ᵥ error) ^ 2 ≤ normSquared a * normSquared error :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a error
  calc
    _ ≤ normSquared a * normSquared error := cauchy
    _ ≤ normSquared a * (delta ^ 2 * lower) :=
      mul_le_mul_of_nonneg_left (sum_error.trans precision) (normSquared_nonneg a)
    _ = delta ^ 2 * (lower * normSquared a) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (envelope a) (sq_nonneg delta)

def roundedCenter (center : Fin n → ℚ) (precision : ℕ) : Fin n → ℚ :=
  fun i => (dyadicCode (center i) precision).value

/-- This lemma applies to the actual dyadically rounded center coordinates;
the precision inequality is quantitative geometry, not a rounding oracle. -/
theorem roundedCenter_support (Q : Matrix (Fin n) (Fin n) ℝ) (lower delta : ℝ)
    (envelope : ∀ x, lower * normSquared x ≤ qform Q x)
    (center : Fin n → ℚ) (precision : ℕ)
    (sufficient : (n : ℝ) * (1 / (2 : ℝ) ^ precision) ^ 2 ≤ delta ^ 2 * lower) :
    ∀ a, (a ⬝ᵥ (fun i => (roundedCenter center precision i : ℝ) - (center i : ℝ))) ^ 2 ≤
      delta ^ 2 * qform Q a := by
  apply coordinateError_support Q lower delta (1 / (2 : ℝ) ^ precision) envelope (by positivity) sufficient
  intro i
  have bound := (dyadic_abs_error (center i) precision).le
  have cast : ((|(dyadicCode (center i) precision).value - center i| : ℚ) : ℝ) ≤
      ((1 / (2 : ℚ) ^ precision : ℚ) : ℝ) := by exact_mod_cast bound
  simpa only [roundedCenter, Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_pow, Rat.cast_one, Rat.cast_ofNat] using cast

end BuyAtBulk.PolynomialLP
