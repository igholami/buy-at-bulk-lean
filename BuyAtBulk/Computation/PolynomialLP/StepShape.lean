import BuyAtBulk.Computation.PolynomialLP.StepRefinement

/-! Positive definiteness and quantitative quadratic envelopes of the actual
stored, rounded shape update. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.PolynomialLP
open scoped Matrix BigOperators
variable {n : ℕ}

theorem stepEta_real (n : ℕ) : (stepEta n : ℝ) = 1 / (64 * (n : ℝ) * (n + 1)) := by
  unfold stepEta
  push_cast
  rfl

theorem stepInflation_real (n : ℕ) : (stepInflation n : ℝ) = (1 + 2 * (stepEta n : ℝ)) ^ 2 := by
  unfold stepInflation
  push_cast
  rfl

theorem stepInflation_range (n : ℕ) (dimension : 2 ≤ n) :
    0 < (stepEta n : ℝ) ∧ 1 ≤ (stepInflation n : ℝ) ∧ (stepInflation n : ℝ) ≤ 2 := by
  have d_ge : (2 : ℝ) ≤ n := by exact_mod_cast dimension
  have denominator : 0 < 64 * (n : ℝ) * (n + 1) := by positivity
  have den_large : (64 : ℝ) ≤ 64 * (n : ℝ) * (n + 1) := by nlinarith
  have eta_le : (stepEta n : ℝ) ≤ 1 / 64 := by
    rw [stepEta_real]
    exact one_div_le_one_div_of_le (by norm_num) den_large
  have eta_pos : 0 < (stepEta n : ℝ) := by rw [stepEta_real]; positivity
  rw [stepInflation_real]
  exact ⟨eta_pos, by nlinarith, by nlinarith⟩

theorem roundShape_hermitian (A : Matrix (Fin n) (Fin n) ℚ) (precision : ℕ)
    (symmetric : (A.map (fun q => (q : ℝ))).IsHermitian) :
    ((roundShape A precision).map (fun q => (q : ℝ))).IsHermitian := by
  have entry_symmetry : ∀ i j, A i j = A j i := by
    intro i j
    apply Rat.cast_injective (α := ℝ)
    have equality := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M j i) symmetric.eq
    simpa only [Matrix.conjTranspose_apply, Matrix.map_apply, star_trivial] using equality
  show ((roundShape A precision).map (fun q => (q : ℝ)))ᴴ = _
  ext i j
  simp [roundShape, Matrix.conjTranspose_apply, Matrix.diagonal_apply, entry_symmetry i j, eq_comm]

theorem roundedStep_positive (state : Ellipsoid n) (direction : Vector ℚ n) (precision : ℕ)
    (positive : (realMatrix state.shape).PosDef) (nonzero : realVector direction ≠ 0) (dimension : 2 ≤ n) :
    (realMatrix (state.roundedStep direction precision).shape).PosDef := by
  obtain ⟨beta_nonneg, beta_le, gamma_ge, _⟩ := cutParameters n dimension
  have central_positive := centralShape_positive _ positive _ nonzero _ _ beta_nonneg (by linarith) (by linarith)
  obtain ⟨_, inflation_ge, _⟩ := stepInflation_range n dimension
  have inflated_symmetric :
      ((((stepInflation n) • rationalMatrix (state.rawShape direction)).map (fun q => (q : ℝ)))).IsHermitian := by
    rw [inflated_rawShape_real]
    exact central_positive.isHermitian.smul (by simp [IsSelfAdjoint])
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [roundedStep_shape_real]
    exact roundShape_hermitian _ _ inflated_symmetric
  · intro x nonzero_x
    have old_positive : 0 < qform (realMatrix (state.rawShape direction)) x := by
      rw [rawShape_real]
      simpa only [qform, star_trivial] using central_positive.dotProduct_mulVec_pos nonzero_x
    have bound := (roundedStep_shape_envelope state direction precision x).1
    have multiplied := mul_le_mul_of_nonneg_right inflation_ge old_positive.le
    simp only [one_mul] at multiplied
    have result := old_positive.trans_le (multiplied.trans bound)
    simpa only [qform, star_trivial, one_mul] using result

theorem roundedStep_bounds (state : Ellipsoid n) (direction : Vector ℚ n) (precision : ℕ)
    (positive : (realMatrix state.shape).PosDef) (nonzero : realVector direction ≠ 0) (dimension : 2 ≤ n)
    (lower upper : ℝ) (upper_ge : (n : ℝ) ≤ upper)
    (old : ∀ x, lower * normSquared x ≤ qform (realMatrix state.shape) x ∧
      qform (realMatrix state.shape) x ≤ upper * normSquared x) :
    ∀ x, (lower / 4) * normSquared x ≤ qform (realMatrix (state.roundedStep direction precision).shape) x ∧
      qform (realMatrix (state.roundedStep direction precision).shape) x ≤ (16 * upper) * normSquared x := by
  intro x
  obtain ⟨shape_lower, shape_upper⟩ := dimensionShape_bounds _ positive _ nonzero dimension x
  rw [← rawShape_real] at shape_lower shape_upper
  obtain ⟨round_lower, round_upper⟩ := roundedStep_shape_envelope state direction precision x
  obtain ⟨_, inflation_lower, inflation_upper⟩ := stepInflation_range n dimension
  have norm_nonneg := normSquared_nonneg x
  have old_nonneg := qform_nonneg _ positive x
  have shape_nonneg : 0 ≤ qform (realMatrix (state.rawShape direction)) x := by linarith
  have inflate_lower := mul_le_mul_of_nonneg_right inflation_lower shape_nonneg
  have inflate_upper := mul_le_mul_of_nonneg_right inflation_upper shape_nonneg
  have tau : (1 : ℝ) / 2 ^ precision ≤ 1 := by
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have small : 2 * (n : ℝ) / (2 : ℝ) ^ precision * normSquared x ≤ 2 * upper * normSquared x := by
    have scaled := mul_le_mul_of_nonneg_left tau (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ) * normSquared x)
    have n_bound := mul_le_mul_of_nonneg_right upper_ge norm_nonneg
    calc
      _ = (2 * (n : ℝ) * normSquared x) * (1 / (2 : ℝ) ^ precision) := by ring
      _ ≤ 2 * (n : ℝ) * normSquared x := by simpa only [mul_one] using scaled
      _ ≤ _ := by nlinarith
  obtain ⟨old_lower, old_upper⟩ := old x
  constructor <;> nlinarith

theorem step_of_positive (state : Ellipsoid n) (direction : Vector ℚ n) (precision : ℕ)
    (positive : (realMatrix state.shape).PosDef) (nonzero : realVector direction ≠ 0) (dimension : 2 ≤ n) :
    state.step direction precision = some (state.roundedStep direction precision) := by
  have q_positive : 0 < qform (realMatrix state.shape) (realVector direction) := by
    simpa only [qform, star_trivial] using positive.dotProduct_mulVec_pos nonzero
  rw [← quadratic_real] at q_positive
  have rational_positive : 0 < quadratic state.shape direction := by exact_mod_cast q_positive
  simp only [Ellipsoid.step, if_neg (by omega : ¬n ≤ 1), if_neg (not_le_of_gt rational_positive)]

end BuyAtBulk.PolynomialLP
