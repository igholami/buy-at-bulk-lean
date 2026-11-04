import BuyAtBulk.Computation.PolynomialLP.SpectralBounds

/-! A contained cube forces a lower determinant bound on its enclosing
ellipsoid. This avoids a separate measure-theoretic volume development. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.PolynomialLP
open scoped Matrix BigOperators
variable {n : ℕ}

def CubeInside (Q : Matrix (Fin n) (Fin n) ℝ) (center base : Fin n → ℝ) (radius : ℝ) : Prop :=
  ∀ point, (∀ i, |point i - base i| ≤ radius) → DualBall Q (point - center)

theorem cube_quadratic_lower (Q : Matrix (Fin n) (Fin n) ℝ) (center base : Fin n → ℝ) (radius : ℝ)
    (radius_nonneg : 0 ≤ radius) (contains : CubeInside Q center base radius) :
    ∀ a, radius ^ 2 * normSquared a ≤ qform Q a := by
  intro a
  let displacement : Fin n → ℝ := fun i => if 0 ≤ a i then radius else -radius
  have displacement_abs : ∀ i, |displacement i| = radius := by
    intro i
    dsimp only [displacement]
    split_ifs <;> simp [abs_of_nonneg radius_nonneg]
  have plus := contains (base + displacement) (by intro i; simpa only [Pi.add_apply, add_sub_cancel_left] using (displacement_abs i).le)
  have minus := contains (base - displacement) (by
    intro i
    have identity : (base - displacement) i - base i = -displacement i := by simp only [Pi.sub_apply]; ring
    rw [identity, abs_neg, displacement_abs])
  have plus_identity : base + displacement - center = (base - center) + displacement := by ext i; simp only [Pi.add_apply, Pi.sub_apply]; ring
  have minus_identity : base - displacement - center = (base - center) - displacement := by ext i; simp only [Pi.sub_apply]; ring
  rw [plus_identity] at plus
  rw [minus_identity] at minus
  have positive_test := plus a
  have negative_test := minus a
  simp only [dotProduct_add, dotProduct_sub] at positive_test negative_test
  have width : (a ⬝ᵥ displacement) ^ 2 ≤ qform Q a := by nlinarith [sq_nonneg (a ⬝ᵥ (base - center))]
  have support : a ⬝ᵥ displacement = radius * ∑ i, |a i| := by
    dsimp only [dotProduct]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [displacement]
    split_ifs with sign
    · rw [abs_of_nonneg sign]; ring
    · rw [abs_of_neg (not_le.mp sign)]; ring
  have norm_bound : normSquared a ≤ (∑ i, |a i|) ^ 2 := by
    have result := Finset.sum_sq_le_sq_sum_of_nonneg (s := (Finset.univ : Finset (Fin n))) (fun i _ => abs_nonneg (a i))
    simpa only [normSquared, sq_abs] using result
  calc
    _ ≤ radius ^ 2 * (∑ i, |a i|) ^ 2 := mul_le_mul_of_nonneg_left norm_bound (sq_nonneg radius)
    _ = (a ⬝ᵥ displacement) ^ 2 := by rw [support]; ring
    _ ≤ _ := width

theorem cube_determinant_lower (Q : Matrix (Fin n) (Fin n) ℝ) (symmetric : Q.IsHermitian)
    (center base : Fin n → ℝ) (radius : ℝ) (radius_nonneg : 0 ≤ radius)
    (contains : CubeInside Q center base radius) :
    radius ^ (2 * n) ≤ Q.det := by
  have bound := determinant_lower Q symmetric (radius ^ 2) (sq_nonneg radius)
    (cube_quadratic_lower Q center base radius radius_nonneg contains)
  simpa only [pow_mul] using bound

end BuyAtBulk.PolynomialLP
