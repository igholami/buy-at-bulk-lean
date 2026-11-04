import BuyAtBulk.Model.RationalLP.Vertices
import BuyAtBulk.Computation.Rational.Encoding
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Int.NatAbs

/-! Work towards polynomial encoding bounds for rational LP optima.
This file proves structural and determinant facts; it does not claim an LP
optimization algorithm or promote finite vertex enumeration to polynomial time. -/
noncomputable section
namespace BuyAtBulk.RationalLP.Problem
open scoped BigOperators
variable {J C : Type} [Fintype J] [Fintype C]

/-- Active constraint forms at a vertex span the full dual space. -/
theorem active_rows_span_dual (P : Problem J C) (x : J → ℚ) (vertex : P.Vertex x) :
    Submodule.span ℚ (P.row '' (P.active x : Set C)) = ⊤ := by
  classical
  let S := Submodule.span ℚ (P.row '' (P.active x : Set C))
  have annihilator_zero : S.dualCoannihilator = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro d member
    change d = 0
    have vanishes : ∀ i ∈ P.active x, P.row i d = 0 := by
      intro i active
      exact (Submodule.mem_dualCoannihilator d).mp member (P.row i)
        (Submodule.subset_span ⟨i, active, rfl⟩)
    have same : x + d = x := by
      apply vertex
      intro i active
      rw [map_add, vanishes i active, add_zero]
      exact (Finset.mem_filter.mp active).2
    exact add_left_cancel (show x + d = x + 0 by simpa using same)
  have dimensions := Subspace.finrank_add_finrank_dualCoannihilator_eq S
  rw [annihilator_zero, finrank_bot, add_zero] at dimensions
  apply Submodule.eq_top_of_finrank_eq
  exact dimensions.trans (Subspace.dual_finrank_eq (K := ℚ) (V := J → ℚ)).symm

/-- A vertex has a square independent family of active constraints. -/
theorem exists_active_basis (P : Problem J C) (x : J → ℚ) (vertex : P.Vertex x) :
    ∃ index : J → C, (∀ j, index j ∈ P.active x) ∧
      LinearIndependent ℚ (fun j => P.row (index j)) := by
  classical
  let rows := P.row '' (P.active x : Set C)
  obtain ⟨chosen, subset, same_span, independent⟩ := exists_linearIndependent ℚ rows
  have finite : chosen.Finite := ((P.active x).finite_toSet.image P.row).subset subset
  letI : Fintype chosen := finite.fintype
  have range_eq : Set.range ((↑) : chosen → Module.Dual ℚ (J → ℚ)) = chosen := by
    ext f
    simp
  let basis : Module.Basis chosen ℚ (Module.Dual ℚ (J → ℚ)) :=
    Module.Basis.mk independent (by rw [range_eq, same_span, P.active_rows_span_dual x vertex])
  have cardinal : Fintype.card chosen = Fintype.card J := by
    rw [← Module.finrank_eq_card_basis basis, Subspace.dual_finrank_eq, Module.finrank_fintype_fun_eq_card]
  let enumeration : J ≃ chosen := Fintype.equivOfCardEq cardinal.symm
  let index : J → C := fun j => Classical.choose (subset (enumeration j).property)
  have member (j : J) : index j ∈ P.active x := (Classical.choose_spec (subset (enumeration j).property)).1
  have row_eq (j : J) : P.row (index j) = (enumeration j).val :=
    (Classical.choose_spec (subset (enumeration j).property)).2
  refine ⟨index, member, ?_⟩
  have family_eq : (fun j => P.row (index j)) = fun j => (enumeration j).val := funext row_eq
  rw [family_eq]
  exact independent.comp enumeration enumeration.injective

variable [DecidableEq J]

def coefficientMap : Module.Dual ℚ (J → ℚ) →ₗ[ℚ] (J → ℚ) where
  toFun form j := form (Pi.single j 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coefficientMap_injective : Function.Injective (coefficientMap (J := J)) := by
  intro f g same
  apply (Pi.basisFun ℚ J).ext
  intro j
  rw [Pi.basisFun_apply]
  have equal := congrFun same j
  change f (Pi.single j 1) = g (Pi.single j 1) at equal
  exact equal

/-- The selected active equalities form a genuinely nonsingular square
system; this is derived from the vertex property, not supplied as a premise. -/
theorem exists_active_matrix (P : Problem J C) (x : J → ℚ) (vertex : P.Vertex x) :
    ∃ index : J → C, (∀ j, index j ∈ P.active x) ∧
      Matrix.det (Matrix.of fun i j => P.row (index i) (Pi.single j 1)) ≠ 0 := by
  obtain ⟨index, member, independent⟩ := P.exists_active_basis x vertex
  refine ⟨index, member, ?_⟩
  have mapped := independent.map' (coefficientMap (J := J))
    (LinearMap.ker_eq_bot.mpr coefficientMap_injective)
  have unit : IsUnit (Matrix.of fun i j => P.row (index i) (Pi.single j 1)) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp mapped
  exact (Matrix.isUnit_iff_isUnit_det _ |>.mp unit).ne_zero

/-- An integral matrix with entries in {-1,0,1} has determinant magnitude at
most d!. This is a value bound with polynomial binary length, not a claim
that determinant expansion is a polynomial-time algorithm. -/
theorem det_natAbs_le_factorial (A : Matrix J J ℤ) (entries : ∀ i j, (A i j).natAbs ≤ 1) :
    A.det.natAbs ≤ (Fintype.card J).factorial := by
  classical
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm J, ((Equiv.Perm.sign σ : ℤ) * ∏ i, A (σ i) i).natAbs :=
      Int.natAbs_sum_le _ _
    _ ≤ ∑ _ : Equiv.Perm J, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro σ _
      rw [Int.natAbs_mul, Int.units_natAbs, one_mul]
      change Int.natAbsHom (∏ i, A (σ i) i) ≤ 1
      rw [map_prod]
      calc
        _ ≤ ∏ _ : J, (1 : ℕ) := Finset.prod_le_prod (fun i _ => entries (σ i) i)
        _ = 1 := by simp
    _ = _ := by simp [Fintype.card_perm]

theorem factorial_lt_binary_square (d : ℕ) : d.factorial < 2 ^ (d * d + 1) := by
  have power : d ^ d ≤ 2 ^ (d * d) := by
    calc
      _ ≤ (2 ^ d) ^ d := Nat.pow_le_pow_left (show d ≤ 2 ^ d from (show d < 2 ^ d from Nat.lt_two_pow_self).le) d
      _ = _ := by rw [← pow_mul]
  have strict : (2 : ℕ) ^ (d * d) < 2 ^ (d * d + 1) := by
    rw [pow_succ]
    have positive : 0 < (2 : ℕ) ^ (d * d) := by positivity
    omega
  exact ((Nat.factorial_le_pow d).trans power).trans_lt strict

def cramerCode (A : Matrix J J ℤ) (b : J → ℤ) (nonzero : A.det ≠ 0) (j : J) :
    BuyAtBulk.Computation.Rational.Code :=
  ⟨(A.updateCol j b).det, A.det, nonzero⟩

/-- Cramer's integer representation has polynomial binary length for a unit
coefficient system. Enumerating all bases is not claimed polynomial. -/
theorem cramerCode_bits (A : Matrix J J ℤ) (b : J → ℤ) (nonzero : A.det ≠ 0)
    (entries : ∀ i j, (A i j).natAbs ≤ 1) (bounds : ∀ i, (b i).natAbs ≤ 1) (j : J) :
    (cramerCode A b nonzero j).bits ≤ 2 * (Fintype.card J) ^ 2 + 4 := by
  have denominator := det_natAbs_le_factorial A entries
  have numerator := det_natAbs_le_factorial (A.updateCol j b) (by
    intro i k
    by_cases same : k = j
    · subst k
      simpa using bounds i
    · simpa [Matrix.updateCol_ne same] using entries i k)
  have budget := factorial_lt_binary_square (Fintype.card J)
  have bounded : (cramerCode A b nonzero j).Bounded ((Fintype.card J) ^ 2 + 1) := by
    constructor
    · exact numerator.trans_lt (by simpa only [pow_two] using budget)
    · exact denominator.trans_lt (by simpa only [pow_two] using budget)
  have encoded := BuyAtBulk.Computation.Rational.Code.bounded_bits bounded
  nlinarith

/-- Exact value of Cramer's integer-pair representation for a solved system. -/
theorem cramerCode_value (A : Matrix J J ℤ) (b : J → ℤ) (nonzero : A.det ≠ 0)
    (x : J → ℚ) (solves : (A.map (Int.castRingHom ℚ)).mulVec x = fun i => (b i : ℚ)) (j : J) :
    (cramerCode A b nonzero j).value = x j := by
  let Aq : Matrix J J ℚ := A.map (Int.castRingHom ℚ)
  have identity : Matrix.cramer Aq (fun i => (b i : ℚ)) = Aq.det • x := by
    rw [Matrix.cramer_eq_adjugate_mulVec, ← solves, Matrix.mulVec_mulVec,
      Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have coordinate := congrFun identity j
  rw [Matrix.cramer_apply] at coordinate
  have numerator : (Aq.updateCol j (fun i => (b i : ℚ))).det =
      ((A.updateCol j b).det : ℚ) := by
    rw [Int.cast_det]
    congr 1
    ext i k
    by_cases same : k = j <;> simp [Aq, Matrix.map_apply, same, Matrix.updateCol_ne]
  rw [numerator] at coordinate
  have denominator : Aq.det = (A.det : ℚ) := (Int.cast_det A).symm
  rw [denominator] at coordinate
  change ((A.updateCol j b).det : ℚ) / (A.det : ℚ) = x j
  apply (div_eq_iff (by exact_mod_cast nonzero)).mpr
  simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using coordinate

end BuyAtBulk.RationalLP.Problem
