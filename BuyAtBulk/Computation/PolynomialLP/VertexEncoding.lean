import BuyAtBulk.Model.RationalLP.VertexEncoding

/-! Polynomial output encoding of attained unit-coefficient rational LP
optima. This supplies a precision foundation for exact optimization; neither
basis enumeration nor optimum selection below is a polynomial algorithm. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.PolynomialLP
open RationalLP RationalLP.Problem Computation.Rational
open scoped BigOperators
variable {J C : Type} [Fintype J] [Fintype C] [DecidableEq J]

theorem linearForm_expansion (form : (J → ℚ) →ₗ[ℚ] ℚ) (x : J → ℚ) :
    form x = ∑ j, form (Pi.single j 1) * x j := by
  have expansion : x = ∑ j, x j • Pi.single j (1 : ℚ) := by
    simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using (Finset.univ_sum_single x).symm
  rw [expansion, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, smul_eq_mul, mul_comm]
  congr 1
  exact congrFun expansion j

theorem vertex_encoded (P : Problem J C) (a : C → J → ℤ) (b : C → ℤ)
    (coefficients : ∀ i j, P.row i (Pi.single j 1) = (a i j : ℚ))
    (rhs : ∀ i, P.bound i = (b i : ℚ))
    (a_unit : ∀ i j, (a i j).natAbs ≤ 1) (b_unit : ∀ i, (b i).natAbs ≤ 1)
    (x : J → ℚ) (vertex : P.Vertex x) :
    ∃ code : J → Code,
      (∀ j, (code j).value = x j) ∧
      (∀ j, (code j).bits ≤ 2 * (Fintype.card J) ^ 2 + 4) := by
  classical
  obtain ⟨index, active, determinant⟩ := P.exists_active_matrix x vertex
  let A : Matrix J J ℤ := fun i j => a (index i) j
  let B : J → ℤ := fun i => b (index i)
  have matrix_eq : Matrix.of (fun i j => P.row (index i) (Pi.single j 1)) = A.map (Int.castRingHom ℚ) := by
    ext i j
    exact coefficients (index i) j
  have determinant_nonzero : A.det ≠ 0 := by
    intro zero
    apply determinant
    rw [matrix_eq, Int.coe_castRingHom, ← Int.cast_det, zero, Int.cast_zero]
  have solves : (A.map (Int.castRingHom ℚ)).mulVec x = fun i => (B i : ℚ) := by
    funext i
    have equality := (Finset.mem_filter.mp (active i)).2
    change P.row (index i) x = P.bound (index i) at equality
    rw [linearForm_expansion, rhs] at equality
    simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, A, B, coefficients, Int.coe_castRingHom] using equality
  refine ⟨fun j => cramerCode A B determinant_nonzero j, ?_, ?_⟩
  · exact fun j => cramerCode_value A B determinant_nonzero x solves j
  · exact fun j => cramerCode_bits A B determinant_nonzero (fun i j => a_unit (index i) j) (fun i => b_unit (index i)) j

/-- A feasible compact LP has an exact optimum with polynomial coordinate
encoding, provided its constraint coefficients and bounds are unit integers.
There is no solution or encoding certificate in the input hypotheses. -/
theorem minimum_encoded (P : Problem J C) (a : C → J → ℤ) (b : C → ℤ)
    (coefficients : ∀ i j, P.row i (Pi.single j 1) = (a i j : ℚ))
    (rhs : ∀ i, P.bound i = (b i : ℚ))
    (a_unit : ∀ i j, (a i j).natAbs ≤ 1) (b_unit : ∀ i, (b i).natAbs ≤ 1)
    (cube : P.InUnitCube) (nonempty : ∃ x, P.Feasible x) :
    ∃ x : J → ℚ, P.Feasible x ∧
      (∀ y, P.Feasible y → P.objective x ≤ P.objective y) ∧
      ∃ code : J → Code, (∀ j, (code j).value = x j) ∧
        (∀ j, (code j).bits ≤ 2 * (Fintype.card J) ^ 2 + 4) := by
  obtain ⟨optimum, feasible, minimal⟩ := P.minimum_attained cube nonempty
  obtain ⟨vertex, vertex_feasible, determined, no_larger⟩ := P.vertex_domination cube optimum feasible
  obtain ⟨code, decoded, bits⟩ := vertex_encoded P a b coefficients rhs a_unit b_unit vertex determined
  exact ⟨vertex, vertex_feasible, fun y hy => no_larger.trans (minimal y hy), code, decoded, bits⟩

end BuyAtBulk.PolynomialLP
