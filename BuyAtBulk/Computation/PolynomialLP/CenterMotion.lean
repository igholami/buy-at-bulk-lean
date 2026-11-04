import BuyAtBulk.Computation.PolynomialLP.StepShape
import BuyAtBulk.Computation.PolynomialLP.MatrixEntries

/-! Magnitude control for the actual center update and its dyadic output.
It depends on the geometric shape envelope, not on the numeric magnitudes of
the separating row, whose scaling cancels through normalization. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.PolynomialLP
open scoped Matrix BigOperators
variable {n : ℕ}

theorem rawCenter_upper (state : Ellipsoid n) (direction : Vector ℚ n)
    (positive : (realMatrix state.shape).PosDef) (nonzero : realVector direction ≠ 0)
    (upper : ℝ) (upper_ge : 1 ≤ upper)
    (shape_upper : ∀ x, qform (realMatrix state.shape) x ≤ upper * normSquared x)
    (center_upper : ∀ i, |realVector state.center i| ≤ upper) :
    ∀ i, |realVector (state.rawCenter direction) i| ≤ 2 * upper := by
  let q := quadratic state.shape direction
  let s : ℝ := normalizationRoot q n
  have q_positive_real : 0 < qform (realMatrix state.shape) (realVector direction) := by
    simpa only [qform, star_trivial] using positive.dotProduct_mulVec_pos nonzero
  have q_positive : 0 < q := by
    rw [← quadratic_real] at q_positive_real
    exact_mod_cast q_positive_real
  obtain ⟨s_positive, root_upper, _⟩ := normalizationRoot_contract q q_positive n
  have s_pos : 0 < s := by
    change (0 : ℝ) < normalizationRoot q n
    exact_mod_cast s_positive
  have root : qform (realMatrix state.shape) (realVector direction) ≤ s ^ 2 := by
    rw [← quadratic_real]
    change (q : ℝ) ≤ (normalizationRoot q n : ℝ) ^ 2
    exact_mod_cast root_upper
  have normalized := normalized_image_upper _ positive _ upper upper_ge shape_upper s s_pos root
  have denominator_ge : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have nn : (0 : ℝ) ≤ n := by positivity
    linarith
  have denominator_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  intro i
  rw [rawCenter_real]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have shift : |(1 / (((n : ℝ) + 1) * s)) * (realMatrix state.shape *ᵥ realVector direction) i| ≤ upper := by
    have identity : (1 / (((n : ℝ) + 1) * s)) * (realMatrix state.shape *ᵥ realVector direction) i =
        ((realMatrix state.shape *ᵥ realVector direction) i / s) / ((n : ℝ) + 1) := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
    rw [identity, abs_div, abs_of_pos denominator_pos]
    apply (div_le_iff₀ denominator_pos).mpr
    exact (normalized i).trans (le_mul_of_one_le_right (by linarith) denominator_ge)
  calc
    _ ≤ |realVector state.center i| + |(1 / (((n : ℝ) + 1) * s)) * (realMatrix state.shape *ᵥ realVector direction) i| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (realVector state.center i) 0
        ((1 / (((n : ℝ) + 1) * s)) * (realMatrix state.shape *ᵥ realVector direction) i)
    _ ≤ upper + upper := add_le_add (center_upper i) shift
    _ = _ := by ring

theorem roundedStep_center_upper (state : Ellipsoid n) (direction : Vector ℚ n) (precision : ℕ)
    (positive : (realMatrix state.shape).PosDef) (nonzero : realVector direction ≠ 0)
    (upper : ℝ) (upper_ge : 1 ≤ upper)
    (shape_upper : ∀ x, qform (realMatrix state.shape) x ≤ upper * normSquared x)
    (center_upper : ∀ i, |realVector state.center i| ≤ upper) :
    ∀ i, |realVector (state.roundedStep direction precision).center i| ≤ 16 * upper := by
  have raw_bound := rawCenter_upper state direction positive nonzero upper upper_ge shape_upper center_upper
  intro i
  have code_error := (dyadic_abs_error (state.rawCenter direction)[i.val] precision).le
  have error : |realVector (state.roundedStep direction precision).center i - realVector (state.rawCenter direction) i| ≤
      1 / (2 : ℝ) ^ precision := by
    have cast : ((|(dyadicCode (state.rawCenter direction)[i.val] precision).value - (state.rawCenter direction)[i.val]| : ℚ) : ℝ) ≤
        ((1 / (2 : ℚ) ^ precision : ℚ) : ℝ) := by exact_mod_cast code_error
    simpa only [realVector, Ellipsoid.roundedStep, Vector.getElem_map, Rat.cast_abs, Rat.cast_sub,
      Rat.cast_div, Rat.cast_pow, Rat.cast_one, Rat.cast_ofNat] using cast
  have tau : (1 : ℝ) / 2 ^ precision ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  calc
    _ = |realVector (state.rawCenter direction) i +
        (realVector (state.roundedStep direction precision).center i - realVector (state.rawCenter direction) i)| := by congr 1; ring
    _ ≤ |realVector (state.rawCenter direction) i| +
        |realVector (state.roundedStep direction precision).center i - realVector (state.rawCenter direction) i| := abs_add_le _ _
    _ ≤ 2 * upper + 1 := add_le_add (raw_bound i) (error.trans tau)
    _ ≤ _ := by linarith

end BuyAtBulk.PolynomialLP
