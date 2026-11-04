import BuyAtBulk.Computation.PolynomialLP.VertexEncoding

/-! Encoding bounds for integer LP data of arbitrary binary magnitude.
This covers non-unit objective cuts after denominator clearing. No magnitude
is used as a loop bound, and no LP optimization algorithm is asserted. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.PolynomialLP
open RationalLP RationalLP.Problem Computation.Rational
open scoped BigOperators
variable {J C : Type} [Fintype J] [Fintype C] [DecidableEq J]

theorem determinant_bound (A : Matrix J J ℤ) (H : ℕ)
    (entries : ∀ i j, (A i j).natAbs ≤ H) :
    A.det.natAbs ≤ (Fintype.card J).factorial * H ^ Fintype.card J := by
  classical
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm J, ((Equiv.Perm.sign σ : ℤ) * ∏ i, A (σ i) i).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _ : Equiv.Perm J, H ^ Fintype.card J := by
      apply Finset.sum_le_sum
      intro σ _
      rw [Int.natAbs_mul, Int.units_natAbs, one_mul]
      change Int.natAbsHom (∏ i, A (σ i) i) ≤ _
      rw [map_prod]
      exact (Finset.prod_le_prod (fun i _ => entries (σ i) i)).trans_eq (by simp)
    _ = _ := by simp [Fintype.card_perm]

theorem factorial_times_power_binary (d H L : ℕ) (magnitude : H ≤ 2 ^ L) :
    d.factorial * H ^ d < 2 ^ (d * d + d * L + 1) := by
  have factorial : d.factorial ≤ 2 ^ (d * d) := by
    calc
      _ ≤ d ^ d := Nat.factorial_le_pow d
      _ ≤ (2 ^ d) ^ d := Nat.pow_le_pow_left (show d ≤ 2 ^ d from Nat.lt_two_pow_self.le) d
      _ = _ := by rw [← pow_mul]
  have power : H ^ d ≤ 2 ^ (d * L) := by
    have bound := Nat.pow_le_pow_left magnitude d
    simpa only [← pow_mul, Nat.mul_comm L d] using bound
  have product := Nat.mul_le_mul factorial power
  rw [← pow_add] at product
  exact product.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))

theorem cramer_bits_general (A : Matrix J J ℤ) (b : J → ℤ) (nonzero : A.det ≠ 0)
    (H L : ℕ) (magnitude : H ≤ 2 ^ L)
    (entries : ∀ i j, (A i j).natAbs ≤ H) (bounds : ∀ i, (b i).natAbs ≤ H) (j : J) :
    (cramerCode A b nonzero j).bits ≤
      2 * ((Fintype.card J) ^ 2 + Fintype.card J * L + 1) + 2 := by
  have denominator := determinant_bound A H entries
  have numerator := determinant_bound (A.updateCol j b) H (by
    intro i k
    by_cases same : k = j
    · subst k; simpa using bounds i
    · simpa [Matrix.updateCol_ne same] using entries i k)
  have binary := factorial_times_power_binary (Fintype.card J) H L magnitude
  apply Code.bounded_bits
  constructor
  · exact numerator.trans_lt (by simpa only [pow_two] using binary)
  · exact denominator.trans_lt (by simpa only [pow_two] using binary)

theorem vertex_encoded_general (P : Problem J C) (a : C → J → ℤ) (b : C → ℤ)
    (coefficients : ∀ i j, P.row i (Pi.single j 1) = (a i j : ℚ))
    (rhs : ∀ i, P.bound i = (b i : ℚ)) (H L : ℕ) (magnitude : H ≤ 2 ^ L)
    (a_bound : ∀ i j, (a i j).natAbs ≤ H) (b_bound : ∀ i, (b i).natAbs ≤ H)
    (x : J → ℚ) (vertex : P.Vertex x) :
    ∃ code : J → Code, (∀ j, (code j).value = x j) ∧
      (∀ j, (code j).bits ≤ 2 * ((Fintype.card J) ^ 2 + Fintype.card J * L + 1) + 2) := by
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
  exact ⟨fun j => cramerCode A B determinant_nonzero j,
    fun j => cramerCode_value A B determinant_nonzero x solves j,
    fun j => cramer_bits_general A B determinant_nonzero H L magnitude
      (fun i j => a_bound (index i) j) (fun i => b_bound (index i)) j⟩

theorem minimum_encoded_general (P : Problem J C) (a : C → J → ℤ) (b : C → ℤ)
    (coefficients : ∀ i j, P.row i (Pi.single j 1) = (a i j : ℚ))
    (rhs : ∀ i, P.bound i = (b i : ℚ)) (H L : ℕ) (magnitude : H ≤ 2 ^ L)
    (a_bound : ∀ i j, (a i j).natAbs ≤ H) (b_bound : ∀ i, (b i).natAbs ≤ H)
    (cube : P.InUnitCube) (nonempty : ∃ x, P.Feasible x) :
    ∃ x : J → ℚ, P.Feasible x ∧
      (∀ y, P.Feasible y → P.objective x ≤ P.objective y) ∧
      ∃ code : J → Code, (∀ j, (code j).value = x j) ∧
        (∀ j, (code j).bits ≤ 2 * ((Fintype.card J) ^ 2 + Fintype.card J * L + 1) + 2) := by
  obtain ⟨optimum, feasible, minimal⟩ := P.minimum_attained cube nonempty
  obtain ⟨vertex, vertex_feasible, determined, no_larger⟩ := P.vertex_domination cube optimum feasible
  obtain ⟨code, decoded, bits⟩ := vertex_encoded_general P a b coefficients rhs H L magnitude a_bound b_bound vertex determined
  exact ⟨vertex, vertex_feasible, fun y hy => no_larger.trans (minimal y hy), code, decoded, bits⟩

end BuyAtBulk.PolynomialLP
