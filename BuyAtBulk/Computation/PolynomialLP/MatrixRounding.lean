import BuyAtBulk.Computation.PolynomialLP.Dyadic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A proved matrix-rounding envelope. Entrywise dyadic rounding plus an
explicit diagonal correction dominates the unrounded quadratic form. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP
open scoped BigOperators
variable {n : ℕ}

def energy (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * A i j * x j

theorem energy_add (A B : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    energy (A + B) x = energy A x + energy B x := by
  simp only [energy, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem energy_sub (A B : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    energy (A - B) x = energy A x - energy B x := by
  simp only [energy, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem energy_diagonal (scale : ℝ) (x : Fin n → ℝ) :
    energy (Matrix.diagonal fun _ : Fin n => scale) x = scale * ∑ i, x i ^ 2 := by
  simp only [energy, Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem energy_bound (E : Matrix (Fin n) (Fin n) ℝ) (delta : ℝ)
    (delta_nonneg : 0 ≤ delta) (entries : ∀ i j, |E i j| ≤ delta) (x : Fin n → ℝ) :
    |energy E x| ≤ (n : ℝ) * delta * ∑ i, x i ^ 2 := by
  have pair_bound (i j : Fin n) : |x i * E i j * x j| ≤ (delta / 2) * (x i ^ 2 + x j ^ 2) := by
    have pair : |x i| * |x j| ≤ (x i ^ 2 + x j ^ 2) / 2 := by
      nlinarith [sq_nonneg (|x i| - |x j|), sq_abs (x i), sq_abs (x j)]
    calc
      _ = |E i j| * (|x i| * |x j|) := by rw [abs_mul, abs_mul]; ring
      _ ≤ delta * (|x i| * |x j|) := mul_le_mul_of_nonneg_right (entries i j) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ ≤ delta * ((x i ^ 2 + x j ^ 2) / 2) := mul_le_mul_of_nonneg_left pair delta_nonneg
      _ = _ := by ring
  calc
    _ ≤ ∑ i, |∑ j, x i * E i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |x i * E i j * x j| := Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, (delta / 2) * (x i ^ 2 + x j ^ 2) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => pair_bound i j
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
      ring

def roundShape (A : Matrix (Fin n) (Fin n) ℚ) (precision : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  (Matrix.of fun i j => (dyadicCode (A i j) precision).value) +
    Matrix.diagonal (fun _ => (n : ℚ) / (2 : ℚ) ^ precision)

/-- For every real vector, the actual rounded matrix is a safe upper envelope
and adds at most 2*n*2^-precision times the squared Euclidean norm. -/
theorem roundShape_envelope (A : Matrix (Fin n) (Fin n) ℚ) (precision : ℕ) (x : Fin n → ℝ) :
    energy (A.map (fun q => (q : ℝ))) x ≤ energy ((roundShape A precision).map (fun q => (q : ℝ))) x ∧
    energy ((roundShape A precision).map (fun q => (q : ℝ))) x ≤
      energy (A.map (fun q => (q : ℝ))) x +
        2 * (n : ℝ) / (2 : ℝ) ^ precision * ∑ i, x i ^ 2 := by
  let rounded : Matrix (Fin n) (Fin n) ℝ := fun i j => ((dyadicCode (A i j) precision).value : ℝ)
  let original : Matrix (Fin n) (Fin n) ℝ := A.map (fun q => (q : ℝ))
  let delta : ℝ := 1 / (2 : ℝ) ^ precision
  have delta_nonneg : 0 ≤ delta := by dsimp [delta]; positivity
  have entry_bound : ∀ i j, |(rounded - original) i j| ≤ delta := by
    intro i j
    have bound := (dyadic_abs_error (A i j) precision).le
    change |((dyadicCode (A i j) precision).value : ℝ) - (A i j : ℝ)| ≤ 1 / (2 : ℝ) ^ precision
    have cast : ((|(dyadicCode (A i j) precision).value - A i j| : ℚ) : ℝ) ≤
        ((1 / (2 : ℚ) ^ precision : ℚ) : ℝ) := by exact_mod_cast bound
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_pow,
      Nat.cast_pow, Nat.cast_ofNat] using cast
  have error := energy_bound (rounded - original) delta delta_nonneg entry_bound x
  rw [energy_sub] at error
  obtain ⟨error_lower, error_upper⟩ := abs_le.mp error
  have identity : (roundShape A precision).map (fun q => (q : ℝ)) =
      rounded + Matrix.diagonal (fun _ => (n : ℝ) * delta) := by
    ext i j
    simp [roundShape, rounded, delta, Matrix.diagonal_apply]
    split_ifs <;> simp [Nat.cast_pow, Rat.cast_pow] <;> ring
  rw [identity, energy_add, energy_diagonal]
  change energy original x ≤ energy rounded x + _ ∧ energy rounded x + _ ≤ energy original x + _
  have correction : 2 * (n : ℝ) / (2 : ℝ) ^ precision * ∑ i, x i ^ 2 =
      2 * ((n : ℝ) * delta * ∑ i, x i ^ 2) := by dsimp [delta]; ring
  rw [correction]
  constructor <;> nlinarith

end BuyAtBulk.PolynomialLP
