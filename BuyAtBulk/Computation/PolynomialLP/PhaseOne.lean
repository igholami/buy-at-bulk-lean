import BuyAtBulk.Computation.PolynomialLP.VertexEncoding
import BuyAtBulk.Computation.PolynomialLP.RationalGap

/-! Quantitative phase-I reduction for bounded unit-coefficient systems.
An infeasible system has a positive minimum violation separated from zero by
an explicit inverse exponential whose exponent is polynomial in dimension.
This reduction does not yet implement a feasibility algorithm. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.PolynomialLP
open RationalLP Computation.Rational
variable {J C : Type} [Fintype J] [Fintype C] [DecidableEq J]

def restrictCoordinates : (Option J → ℚ) →ₗ[ℚ] (J → ℚ) where
  toFun x j := x (some j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def phaseOne (P : Problem J C) : Problem (Option J) (C ⊕ (Bool × Option J)) where
  row
    | .inl i => P.row i ∘ₗ restrictCoordinates - LinearMap.proj none
    | .inr (upper, j) => if upper then LinearMap.proj j else -LinearMap.proj j
  bound
    | .inl i => P.bound i
    | .inr (upper, _) => if upper then 1 else 0
  objective := LinearMap.proj none

theorem phaseOne_in_cube (P : Problem J C) : (phaseOne P).InUnitCube := by
  intro x feasible j
  have lower := feasible (.inr (false, j))
  have upper := feasible (.inr (true, j))
  simpa only [phaseOne, Bool.false_eq_true, ↓reduceIte, LinearMap.neg_apply,
    LinearMap.proj_apply, neg_nonpos] using And.intro lower upper

def phasePoint (x : J → ℚ) (violation : ℚ) : Option J → ℚ
  | none => violation
  | some j => x j

theorem phasePoint_feasible (P : Problem J C) (x : J → ℚ) (violation : ℚ)
    (box : ∀ j, 0 ≤ x j ∧ x j ≤ 1) (lower : 0 ≤ violation) (upper : violation ≤ 1)
    (rows : ∀ i, P.row i x ≤ P.bound i + violation) :
    (phaseOne P).Feasible (phasePoint x violation) := by
  intro c
  cases c with
  | inl i =>
    change P.row i x - violation ≤ P.bound i
    linarith [rows i]
  | inr c =>
    rcases c with ⟨bound, j⟩
    cases j with
    | none =>
      cases bound
      · simpa [phaseOne, phasePoint] using (show -violation ≤ 0 from by linarith)
      · simpa [phaseOne, phasePoint] using upper
    | some j =>
      cases bound
      · simpa [phaseOne, phasePoint] using (show -x j ≤ 0 from by linarith [(box j).1])
      · simpa [phaseOne, phasePoint] using (box j).2

theorem phaseOne_zero (P : Problem J C) (x : Option J → ℚ)
    (feasible : (phaseOne P).Feasible x) (zero : x none = 0) :
    P.Feasible (restrictCoordinates x) := by
  intro i
  have row := feasible (.inl i)
  change P.row i (restrictCoordinates x) - x none ≤ P.bound i at row
  simpa only [zero, sub_zero] using row

def phaseCoefficients (a : C → J → ℤ) : C ⊕ (Bool × Option J) → Option J → ℤ
  | .inl i, none => -1
  | .inl i, some j => a i j
  | .inr (upper, j), k => if j = k then (if upper then 1 else -1) else 0

def phaseBounds (b : C → ℤ) : C ⊕ (Bool × Option J) → ℤ
  | .inl i => b i
  | .inr (upper, _) => if upper then 1 else 0

theorem phaseCoefficients_correct (P : Problem J C) (a : C → J → ℤ)
    (coefficients : ∀ i j, P.row i (Pi.single j 1) = (a i j : ℚ)) :
    ∀ i j, (phaseOne P).row i (Pi.single j 1) = (phaseCoefficients a i j : ℚ) := by
  classical
  intro c j
  cases c with
  | inl i =>
    cases j with
    | none =>
      have restricted : restrictCoordinates (Pi.single none (1 : ℚ)) = (0 : J → ℚ) := by
        ext j
        simp [restrictCoordinates, Pi.single_apply]
      simp [phaseOne, phaseCoefficients, LinearMap.comp_apply, restricted]
    | some j =>
      have restricted : restrictCoordinates (Pi.single (some j) (1 : ℚ)) = Pi.single j 1 := by
        ext k
        simp [restrictCoordinates, Pi.single_apply]
      simp [phaseOne, phaseCoefficients, LinearMap.comp_apply, restricted, coefficients]
  | inr c =>
    rcases c with ⟨upper, k⟩
    cases upper <;> by_cases same : k = j <;> simp [phaseOne, phaseCoefficients, same, Pi.single_apply, eq_comm]

theorem phaseBounds_correct (P : Problem J C) (b : C → ℤ) (rhs : ∀ i, P.bound i = (b i : ℚ)) :
    ∀ i, (phaseOne P).bound i = (phaseBounds b i : ℚ) := by
  intro c
  cases c with
  | inl i => exact rhs i
  | inr c => rcases c with ⟨upper, j⟩; cases upper <;> rfl

theorem phaseCoefficients_unit (a : C → J → ℤ) (unit : ∀ i j, (a i j).natAbs ≤ 1) :
    ∀ i j, (phaseCoefficients a i j).natAbs ≤ 1 := by
  intro c j
  cases c with
  | inl i => cases j <;> simp [phaseCoefficients, unit]
  | inr c =>
    rcases c with ⟨upper, k⟩
    cases upper <;> by_cases same : k = j <;> simp [phaseCoefficients, same]

theorem phaseBounds_unit (b : C → ℤ) (unit : ∀ i, (b i).natAbs ≤ 1) :
    ∀ i : C ⊕ (Bool × Option J), (phaseBounds b i).natAbs ≤ 1 := by
  intro c
  cases c with
  | inl i => exact unit i
  | inr c => rcases c with ⟨upper, j⟩; cases upper <;> simp [phaseBounds]

theorem phaseOne_nonempty (P : Problem J C) (b : C → ℤ)
    (rhs : ∀ i, P.bound i = (b i : ℚ)) (unit : ∀ i, (b i).natAbs ≤ 1) :
    ∃ x, (phaseOne P).Feasible x := by
  refine ⟨phasePoint (fun _ => 0) 1, phasePoint_feasible P _ _ (by norm_num) (by norm_num) le_rfl ?_⟩
  intro i
  have cast_bound : ((b i).natAbs : ℤ) ≤ 1 := by exact_mod_cast unit i
  rw [Int.natCast_natAbs] at cast_bound
  have lower : (-1 : ℚ) ≤ (b i : ℚ) := by exact_mod_cast (abs_le.mp cast_bound).1
  change P.row i (0 : J → ℚ) ≤ P.bound i + 1
  rw [map_zero, rhs]
  linarith

/-- An explicit binary precision suffices to distinguish phase-I optimum zero
from a strictly positive optimum. No optimizer certificate is assumed. -/
theorem phaseOne_gap (P : Problem J C) (a : C → J → ℤ) (b : C → ℤ)
    (coefficients : ∀ i j, P.row i (Pi.single j 1) = (a i j : ℚ))
    (rhs : ∀ i, P.bound i = (b i : ℚ))
    (a_unit : ∀ i j, (a i j).natAbs ≤ 1) (b_unit : ∀ i, (b i).natAbs ≤ 1) :
    ∃ optimum : Option J → ℚ,
      (phaseOne P).Feasible optimum ∧
      (∀ y, (phaseOne P).Feasible y → optimum none ≤ y none) ∧
      (optimum none = 0 ∨
        1 / (2 : ℚ) ^ (2 * (Fintype.card J + 1) ^ 2 + 5) ≤ optimum none) := by
  obtain ⟨optimum, feasible, minimal, code, decoded, bits⟩ :=
    minimum_encoded (phaseOne P) (phaseCoefficients a) (phaseBounds b)
      (phaseCoefficients_correct P a coefficients) (phaseBounds_correct P b rhs)
      (phaseCoefficients_unit a a_unit) (phaseBounds_unit b b_unit) (phaseOne_in_cube P)
      (phaseOne_nonempty P b rhs b_unit)
  refine ⟨optimum, feasible, minimal, ?_⟩
  by_cases zero : optimum none = 0
  · exact Or.inl zero
  · apply Or.inr
    have positive : 0 < optimum none := lt_of_le_of_ne ((phaseOne_in_cube P) optimum feasible none).1 (Ne.symm zero)
    have normalized : (Code.ofRat (optimum none)).bits ≤ 2 * (Fintype.card (Option J)) ^ 2 + 4 := by
      rw [← decoded none]
      exact (Code.normalized_bits_le _).trans (bits none)
    have lower := positive_encoding_lower (optimum none) _ positive normalized
    simpa only [Fintype.card_option, Nat.add_assoc] using lower

/-- Relaxed feasibility below the proved phase-I gap implies exact rational
feasibility. This is a precision reduction, not an assumed solver interface. -/
theorem exact_of_small_violation (P : Problem J C) (a : C → J → ℤ) (b : C → ℤ)
    (coefficients : ∀ i j, P.row i (Pi.single j 1) = (a i j : ℚ))
    (rhs : ∀ i, P.bound i = (b i : ℚ))
    (a_unit : ∀ i j, (a i j).natAbs ≤ 1) (b_unit : ∀ i, (b i).natAbs ≤ 1)
    (x : J → ℚ) (box : ∀ j, 0 ≤ x j ∧ x j ≤ 1) (epsilon : ℚ)
    (epsilon_nonneg : 0 ≤ epsilon) (epsilon_le : epsilon ≤ 1)
    (precision : epsilon < 1 / (2 : ℚ) ^ (2 * (Fintype.card J + 1) ^ 2 + 5))
    (approximate : ∀ i, P.row i x ≤ P.bound i + epsilon) :
    ∃ y, P.Feasible y := by
  obtain ⟨optimum, feasible, minimal, zero | gap⟩ := phaseOne_gap P a b coefficients rhs a_unit b_unit
  · exact ⟨restrictCoordinates optimum, phaseOne_zero P optimum feasible zero⟩
  · have bounded := minimal (phasePoint x epsilon)
      (phasePoint_feasible P x epsilon box epsilon_nonneg epsilon_le approximate)
    change optimum none ≤ epsilon at bounded
    linarith

end BuyAtBulk.PolynomialLP
