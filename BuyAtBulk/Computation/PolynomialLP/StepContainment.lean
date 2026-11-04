import BuyAtBulk.Computation.PolynomialLP.StepShape

/-! Containment of the actual rational/dyadically rounded update. All accuracy
premises are explicit numerical precision inequalities; the loop's fixed
polynomial precision schedule discharges them uniformly. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace BuyAtBulk.PolynomialLP
open scoped Matrix BigOperators
variable {n : ℕ}

theorem roundedStep_contains (state : Ellipsoid n) (direction : Vector ℚ n) (precision : ℕ)
    (positive : (realMatrix state.shape).PosDef) (nonzero : realVector direction ≠ 0) (dimension : 2 ≤ n)
    (lower : ℝ) (envelope : ∀ x, lower * normSquared x ≤ qform (realMatrix state.shape) x)
    (enough : (n : ℝ) * (1 / (2 : ℝ) ^ precision) ^ 2 ≤ (stepEta n : ℝ) ^ 2 * (lower / 4))
    (point : Fin n → ℝ) (inside : DualBall (realMatrix state.shape) (point - realVector state.center))
    (cut : realVector direction ⬝ᵥ (point - realVector state.center) ≤ 0) :
    DualBall (realMatrix (state.roundedStep direction precision).shape)
      (point - realVector (state.roundedStep direction precision).center) := by
  let Q := realMatrix state.shape
  let a := realVector direction
  let C := centralShape Q a (cutBeta n) (cutGamma n)
  let eta : ℝ := stepEta n
  let q := quadratic state.shape direction
  have q_positive_real : 0 < qform Q a := by simpa only [qform, star_trivial] using positive.dotProduct_mulVec_pos nonzero
  have q_positive : 0 < q := by
    have cast : (0 : ℝ) < q := by simpa only [q, quadratic_real] using q_positive_real
    exact_mod_cast cast
  obtain ⟨root_positive, root_upper, _⟩ := normalizationRoot_contract q q_positive n
  have root_positive_real : (0 : ℝ) < normalizationRoot q n := by exact_mod_cast root_positive
  have root_upper_real : qform Q a ≤ (normalizationRoot q n : ℝ) ^ 2 := by
    rw [← quadratic_real]
    exact_mod_cast root_upper
  have raw := centralShape_contains_matrix Q positive a (point - realVector state.center) nonzero dimension
    inside cut (normalizationRoot q n : ℝ) root_positive_real root_upper_real
  have q_identity : qform Q a = (q : ℝ) := (quadratic_real state.shape direction).symm
  rw [q_identity] at raw
  obtain ⟨displacement_nonneg, displacement_small⟩ := normalization_displacement q q_positive n dimension
  obtain ⟨eta_positive, _, _⟩ := stepInflation_range n dimension
  have displacement_eta : (1 - Real.sqrt (q : ℝ) / (normalizationRoot q n : ℝ)) / (n : ℝ) ≤ eta := by
    apply displacement_small.trans
    dsimp only [eta]
    rw [stepEta_real]
    have d_ge : (2 : ℝ) ≤ n := by exact_mod_cast dimension
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  obtain ⟨beta_nonneg, beta_le, gamma_ge, _⟩ := cutParameters n dimension
  have C_positive : C.PosDef := centralShape_positive Q positive a nonzero _ _ beta_nonneg (by linarith) (by linarith)
  have C_envelope : ∀ x, (lower / 4) * normSquared x ≤ qform C x := by
    intro x
    have base := envelope x
    have cut_bound := (dimensionShape_bounds Q positive a nonzero dimension x).1
    dsimp only [C]
    linarith
  have enlarged : DualBall (((1 + eta) ^ 2) • C)
      ((point - realVector state.center) + (1 / (((n : ℝ) + 1) * (normalizationRoot q n : ℝ))) • (Q *ᵥ a)) := by
    apply dualBall_mono _ _ (fun x => ?_) _ raw
    simp only [qform, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    have square : (1 + (1 - Real.sqrt (q : ℝ) / (normalizationRoot q n : ℝ)) / (n : ℝ)) ^ 2 ≤ (1 + eta) ^ 2 := by
      nlinarith
    exact mul_le_mul_of_nonneg_right square (qform_nonneg C C_positive x)
  have raw_translation :
      (point - realVector state.center) + (1 / (((n : ℝ) + 1) * (normalizationRoot q n : ℝ))) • (Q *ᵥ a) =
      point - realVector (state.rawCenter direction) := by
    rw [rawCenter_real]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [raw_translation] at enlarged
  have error_bound := roundedCenter_support C (lower / 4) eta C_envelope
    (fun i : Fin n => (state.rawCenter direction)[i.val]) precision enough
  have small : ∀ x, (x ⬝ᵥ (realVector (state.roundedStep direction precision).center -
      realVector (state.rawCenter direction))) ^ 2 ≤ eta ^ 2 * qform C x := by
    have vector_eq : realVector (state.roundedStep direction precision).center - realVector (state.rawCenter direction) =
        fun i => (roundedCenter (fun j : Fin n => (state.rawCenter direction)[j.val]) precision i : ℝ) -
          ((state.rawCenter direction)[i.val] : ℝ) := by
      rw [roundedStep_center_real]
      rfl
    intro x
    rw [vector_eq]
    exact error_bound x
  have contained := dualBall_shift_radius C (point - realVector (state.rawCenter direction))
    (realVector (state.roundedStep direction precision).center - realVector (state.rawCenter direction))
    (1 + eta) eta (by linarith) eta_positive enlarged small
  have radius_eq : (1 + eta + eta) ^ 2 = (stepInflation n : ℝ) := by
    rw [stepInflation_real]
    dsimp only [eta]
    ring
  have translation : (point - realVector (state.rawCenter direction)) -
      (realVector (state.roundedStep direction precision).center - realVector (state.rawCenter direction)) =
      point - realVector (state.roundedStep direction precision).center := by ext i; simp only [Pi.sub_apply]; ring
  rw [radius_eq, translation] at contained
  apply dualBall_mono _ _ (fun x => ?_) _ contained
  have bound := (roundedStep_shape_envelope state direction precision x).1
  rw [rawShape_real] at bound
  simpa only [qform, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] using bound

end BuyAtBulk.PolynomialLP
