import BuyAtBulk.Model.RationalLP.Problem

/-! Rational improving directions and boundedness of feasible rays. -/
noncomputable section
namespace BuyAtBulk.RationalLP.Problem
variable {J C : Type} [Fintype J] [Fintype C] (P : Problem J C)

omit [Fintype J] in
/-- If active equalities do not uniquely determine a point, there is a nonzero
rational direction annihilating them and not increasing the objective. -/
theorem improving_direction (x : J → ℚ) (not_vertex : ¬P.Vertex x) :
    ∃ d : J → ℚ, d ≠ 0 ∧ (∀ i ∈ P.active x, P.row i d = 0) ∧
      P.objective d ≤ 0 := by
  classical
  have hy : ∃ y : J → ℚ, (∀ i ∈ P.active x, P.row i y = P.bound i) ∧ y ≠ x := by
    have hh : ∃ y : J → ℚ, ¬((∀ i ∈ P.active x, P.row i y = P.bound i) → y = x) :=
      not_forall.mp not_vertex
    obtain ⟨y, hy⟩ := hh
    exact ⟨y, not_imp.mp hy⟩
  obtain ⟨y, hy, hyne⟩ := hy
  let d := y - x
  have dne : d ≠ 0 := sub_ne_zero.mpr hyne
  have hdir : ∀ i ∈ P.active x, P.row i d = 0 := by
    intro i hi
    have hix : P.row i x = P.bound i := (Finset.mem_filter.mp hi).2
    simp [d, map_sub, hy i hi, hix]
  by_cases ho : P.objective d ≤ 0
  · exact ⟨d, dne, hdir, ho⟩
  · refine ⟨-d, neg_ne_zero.mpr dne, ?_, ?_⟩
    · intro i hi; simp [map_neg, hdir i hi]
    · simp only [map_neg]; linarith

/-- Unit-cube boundedness rules out every nonzero feasible ray. Therefore any
nonzero direction has a constraint whose derivative is strictly positive. -/
theorem positive_row (cube : P.InUnitCube) (x d : J → ℚ)
    (hx : P.Feasible x) (dne : d ≠ 0) : ∃ i, 0 < P.row i d := by
  classical
  by_contra hn
  have rows_nonpos : ∀ i, P.row i d ≤ 0 := by simpa using hn
  have ray : ∀ a : ℚ, 0 ≤ a → P.Feasible (x + a • d) := by
    intro a ha i
    have hprod := mul_nonpos_of_nonneg_of_nonpos ha (rows_nonpos i)
    have hix := hx i
    simp only [map_add, map_smul, smul_eq_mul]
    linarith
  obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by
    by_contra hn
    apply dne
    ext j
    simpa using not_exists.mp hn j
  have xcube := cube x hx j
  rcases lt_or_gt_of_ne hj with hneg | hpos
  · let a : ℚ := -2 / d j
    have ha : 0 ≤ a := le_of_lt (div_pos_of_neg_of_neg (by norm_num) hneg)
    have acube := cube (x + a • d) (ray a ha) j
    have hvalue : (x + a • d) j = x j - 2 := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, a]
      field_simp
      ring
    rw [hvalue] at acube
    linarith
  · let a : ℚ := 2 / d j
    have ha : 0 ≤ a := div_nonneg (by norm_num) (le_of_lt hpos)
    have acube := cube (x + a • d) (ray a ha) j
    have hvalue : (x + a • d) j = x j + 2 := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, a]
      field_simp
    rw [hvalue] at acube
    linarith

end BuyAtBulk.RationalLP.Problem
