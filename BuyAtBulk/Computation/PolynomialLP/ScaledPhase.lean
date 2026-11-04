import BuyAtBulk.Computation.PolynomialLP.PhaseOne
import BuyAtBulk.Computation.PolynomialLP.IntegerEncoding

/-! Phase-I precision for arbitrary integer coefficient magnitudes. Objective
cuts with rational binary coefficients can be denominator-cleared and handled
here; no unit-coefficient assumption is made for such cuts. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.PolynomialLP
open RationalLP Computation.Rational
variable {J C : Type} [Fintype J] [Fintype C] [DecidableEq J]

def scaledPhase (P : Problem J C) (H : ℕ) : Problem (Option J) (C ⊕ (Bool × Option J)) where
  row
    | .inl i => P.row i ∘ₗ restrictCoordinates - (H : ℚ) • LinearMap.proj none
    | .inr (upper, j) => if upper then LinearMap.proj j else -LinearMap.proj j
  bound
    | .inl i => P.bound i
    | .inr (upper, _) => if upper then 1 else 0
  objective := LinearMap.proj none

theorem scaledPhase_in_cube (P : Problem J C) (H : ℕ) : (scaledPhase P H).InUnitCube := by
  intro x feasible j
  have lower := feasible (.inr (false, j))
  have upper := feasible (.inr (true, j))
  simpa only [scaledPhase, Bool.false_eq_true, ↓reduceIte, LinearMap.neg_apply,
    LinearMap.proj_apply, neg_nonpos] using And.intro lower upper

theorem scaledPoint_feasible (P : Problem J C) (H : ℕ) (x : J → ℚ) (violation : ℚ)
    (box : ∀ j, 0 ≤ x j ∧ x j ≤ 1) (lower : 0 ≤ violation) (upper : violation ≤ 1)
    (rows : ∀ i, P.row i x ≤ P.bound i + H * violation) :
    (scaledPhase P H).Feasible (phasePoint x violation) := by
  intro c
  cases c with
  | inl i => change P.row i x - H * violation ≤ P.bound i; linarith [rows i]
  | inr c =>
    rcases c with ⟨bound, j⟩
    cases j with
    | none =>
      cases bound
      · simpa [scaledPhase, phasePoint] using (show -violation ≤ 0 from by linarith)
      · simpa [scaledPhase, phasePoint] using upper
    | some j =>
      cases bound
      · simpa [scaledPhase, phasePoint] using (show -x j ≤ 0 from by linarith [(box j).1])
      · simpa [scaledPhase, phasePoint] using (box j).2

theorem scaledPhase_zero (P : Problem J C) (H : ℕ) (x : Option J → ℚ)
    (feasible : (scaledPhase P H).Feasible x) (zero : x none = 0) : P.Feasible (restrictCoordinates x) := by
  intro i
  have row := feasible (.inl i)
  change P.row i (restrictCoordinates x) - H * x none ≤ P.bound i at row
  simpa only [zero, mul_zero, sub_zero] using row

def scaledCoefficients (a : C → J → ℤ) (H : ℕ) : C ⊕ (Bool × Option J) → Option J → ℤ
  | .inl _, none => -(H : ℤ)
  | .inl i, some j => a i j
  | .inr (upper, j), k => if j = k then (if upper then 1 else -1) else 0

theorem scaledCoefficients_correct (P : Problem J C) (a : C → J → ℤ) (H : ℕ)
    (coefficients : ∀ i j, P.row i (Pi.single j 1) = (a i j : ℚ)) :
    ∀ i j, (scaledPhase P H).row i (Pi.single j 1) = (scaledCoefficients a H i j : ℚ) := by
  classical
  intro c j
  cases c with
  | inl i =>
    cases j with
    | none =>
      have restricted : restrictCoordinates (Pi.single none (1 : ℚ)) = (0 : J → ℚ) := by ext j; simp [restrictCoordinates]
      simp [scaledPhase, scaledCoefficients, LinearMap.comp_apply, restricted]
    | some j =>
      have restricted : restrictCoordinates (Pi.single (some j) (1 : ℚ)) = Pi.single j 1 := by ext k; simp [restrictCoordinates, Pi.single_apply]
      simp [scaledPhase, scaledCoefficients, LinearMap.comp_apply, restricted, coefficients]
  | inr c => rcases c with ⟨upper, k⟩; cases upper <;> by_cases same : k = j <;> simp [scaledPhase, scaledCoefficients, same, eq_comm]

theorem scaledCoefficients_bound (a : C → J → ℤ) (H : ℕ) (H_pos : 0 < H)
    (bound : ∀ i j, (a i j).natAbs ≤ H) : ∀ i j, (scaledCoefficients a H i j).natAbs ≤ H := by
  intro c j
  cases c with
  | inl i => cases j <;> simp [scaledCoefficients, bound]
  | inr c =>
    rcases c with ⟨upper, k⟩
    cases upper <;> by_cases same : k = j <;> simp [scaledCoefficients, same] <;> omega

theorem scaledPhase_nonempty (P : Problem J C) (H : ℕ) (b : C → ℤ)
    (rhs : ∀ i, P.bound i = (b i : ℚ)) (bound : ∀ i, (b i).natAbs ≤ H) :
    ∃ x, (scaledPhase P H).Feasible x := by
  refine ⟨phasePoint (fun _ => 0) 1, scaledPoint_feasible P H _ _ (by norm_num) (by norm_num) le_rfl ?_⟩
  intro i
  have cast_bound : ((b i).natAbs : ℤ) ≤ H := by exact_mod_cast bound i
  rw [Int.natCast_natAbs] at cast_bound
  have lower : -(H : ℚ) ≤ (b i : ℚ) := by exact_mod_cast (abs_le.mp cast_bound).1
  change P.row i (0 : J → ℚ) ≤ P.bound i + H * 1
  rw [map_zero, rhs]
  linarith

theorem scaledPhase_gap (P : Problem J C) (a : C → J → ℤ) (b : C → ℤ) (H L : ℕ)
    (H_pos : 0 < H) (magnitude : H ≤ 2 ^ L)
    (coefficients : ∀ i j, P.row i (Pi.single j 1) = (a i j : ℚ)) (rhs : ∀ i, P.bound i = (b i : ℚ))
    (a_bound : ∀ i j, (a i j).natAbs ≤ H) (b_bound : ∀ i, (b i).natAbs ≤ H) :
    ∃ optimum : Option J → ℚ, (scaledPhase P H).Feasible optimum ∧
      (∀ y, (scaledPhase P H).Feasible y → optimum none ≤ y none) ∧
      (optimum none = 0 ∨
        1 / (2 : ℚ) ^ (2 * ((Fintype.card J + 1) ^ 2 + (Fintype.card J + 1) * L + 1) + 3) ≤ optimum none) := by
  have rhs_correct : ∀ i, (scaledPhase P H).bound i = (phaseBounds b i : ℚ) := by
    intro c
    cases c with
    | inl i => exact rhs i
    | inr c => rcases c with ⟨upper, j⟩; cases upper <;> rfl
  have rhs_bound : ∀ i : C ⊕ (Bool × Option J), (phaseBounds b i).natAbs ≤ H := by
    intro c
    cases c with
    | inl i => exact b_bound i
    | inr c => rcases c with ⟨upper, j⟩; cases upper <;> simp [phaseBounds] <;> omega
  obtain ⟨optimum, feasible, minimal, code, decoded, bits⟩ :=
    minimum_encoded_general (scaledPhase P H) (scaledCoefficients a H) (phaseBounds b)
      (scaledCoefficients_correct P a H coefficients) rhs_correct H L magnitude
      (scaledCoefficients_bound a H H_pos a_bound) rhs_bound (scaledPhase_in_cube P H)
      (scaledPhase_nonempty P H b rhs b_bound)
  refine ⟨optimum, feasible, minimal, ?_⟩
  by_cases zero : optimum none = 0
  · exact Or.inl zero
  · apply Or.inr
    have positive : 0 < optimum none := lt_of_le_of_ne ((scaledPhase_in_cube P H) optimum feasible none).1 (Ne.symm zero)
    have normalized : (Code.ofRat (optimum none)).bits ≤
        2 * ((Fintype.card (Option J)) ^ 2 + Fintype.card (Option J) * L + 1) + 2 := by
      rw [← decoded none]
      exact (Code.normalized_bits_le _).trans (bits none)
    simpa only [Fintype.card_option, Nat.add_assoc] using positive_encoding_lower (optimum none) _ positive normalized

end BuyAtBulk.PolynomialLP
