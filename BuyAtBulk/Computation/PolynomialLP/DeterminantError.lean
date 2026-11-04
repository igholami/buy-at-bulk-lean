import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Quantitative determinant sensitivity to entrywise rounding. The factorial
is a value bound whose binary logarithm is polynomial; no determinant
expansion is used as the proposed optimization algorithm. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.PolynomialLP
open scoped BigOperators
variable {J : Type} [DecidableEq J] [Fintype J]

theorem product_difference_bound (indices : Finset J) (f g : J → ℝ) (M delta : ℝ)
    (M_nonneg : 0 ≤ M) (delta_nonneg : 0 ≤ delta)
    (f_bound : ∀ i ∈ indices, |f i| ≤ M) (g_bound : ∀ i ∈ indices, |g i| ≤ M)
    (difference : ∀ i ∈ indices, |f i - g i| ≤ delta) :
    |(∏ i ∈ indices, f i) - ∏ i ∈ indices, g i| ≤
      (indices.card : ℝ) * delta * (M + 1) ^ indices.card := by
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert i rest absent ih =>
    have f_i := f_bound i (Finset.mem_insert_self _ _)
    have difference_i := difference i (Finset.mem_insert_self _ _)
    have tail := ih (fun j member => f_bound j (Finset.mem_insert_of_mem member))
      (fun j member => g_bound j (Finset.mem_insert_of_mem member))
      (fun j member => difference j (Finset.mem_insert_of_mem member))
    have g_product : |∏ j ∈ rest, g j| ≤ (M + 1) ^ rest.card := by
      rw [Finset.abs_prod]
      calc
        _ ≤ ∏ _j ∈ rest, (M + 1) := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
          (fun j member => (g_bound j (Finset.mem_insert_of_mem member)).trans (by linarith))
        _ = _ := by simp
    rw [Finset.prod_insert absent, Finset.prod_insert absent]
    have decomposition : f i * (∏ j ∈ rest, f j) - g i * (∏ j ∈ rest, g j) =
        f i * ((∏ j ∈ rest, f j) - ∏ j ∈ rest, g j) + (f i - g i) * (∏ j ∈ rest, g j) := by ring
    rw [decomposition]
    calc
      _ ≤ |f i * ((∏ j ∈ rest, f j) - ∏ j ∈ rest, g j)| + |(f i - g i) * (∏ j ∈ rest, g j)| := abs_add_le _ _
      _ = |f i| * |(∏ j ∈ rest, f j) - ∏ j ∈ rest, g j| + |f i - g i| * |∏ j ∈ rest, g j| := by rw [abs_mul, abs_mul]
      _ ≤ M * ((rest.card : ℝ) * delta * (M + 1) ^ rest.card) + delta * (M + 1) ^ rest.card := by
        exact add_le_add (mul_le_mul f_i tail (abs_nonneg _) M_nonneg)
          (mul_le_mul difference_i g_product (abs_nonneg _) delta_nonneg)
      _ ≤ ((rest.card + 1 : ℕ) : ℝ) * delta * (M + 1) ^ (rest.card + 1) := by
        rw [pow_succ, Nat.cast_succ]
        have nonneg := mul_nonneg (show 0 ≤ M + (rest.card : ℝ) by positivity)
          (mul_nonneg delta_nonneg (pow_nonneg (show 0 ≤ M + 1 by linarith) rest.card))
        nlinarith
      _ = _ := by rw [Finset.card_insert_of_notMem absent]

theorem determinant_difference_bound (A B : Matrix J J ℝ) (M delta : ℝ)
    (M_nonneg : 0 ≤ M) (delta_nonneg : 0 ≤ delta)
    (A_bound : ∀ i j, |A i j| ≤ M) (B_bound : ∀ i j, |B i j| ≤ M)
    (difference : ∀ i j, |A i j - B i j| ≤ delta) :
    |A.det - B.det| ≤ (Fintype.card J).factorial * Fintype.card J * delta * (M + 1) ^ Fintype.card J := by
  classical
  rw [Matrix.det_apply', Matrix.det_apply', ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ σ : Equiv.Perm J, |((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ i, A (σ i) i) -
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ i, B (σ i) i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Equiv.Perm J, (Fintype.card J : ℝ) * delta * (M + 1) ^ Fintype.card J := by
      apply Finset.sum_le_sum
      intro σ _
      have bound := product_difference_bound (Finset.univ : Finset J) (fun i => A (σ i) i) (fun i => B (σ i) i) M delta
        M_nonneg delta_nonneg (fun i _ => A_bound (σ i) i) (fun i _ => B_bound (σ i) i) (fun i _ => difference (σ i) i)
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with sign | sign
      · simpa [sign] using bound
      · simp only [sign, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul]
        have rearrange : -(∏ i, A (σ i) i) - -(∏ i, B (σ i) i) = -((∏ i, A (σ i) i) - ∏ i, B (σ i) i) := by ring
        rw [rearrange, abs_neg]
        simpa using bound
    _ = _ := by simp [Fintype.card_perm]; ring

end BuyAtBulk.PolynomialLP
