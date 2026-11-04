import BuyAtBulk.Computation.PolynomialLP.ObjectivePrecision
import BuyAtBulk.Computation.PolynomialLP.ObjectiveSearch

/-! Uniform integer brackets and polynomial bisection precision. The decision
procedure is still supplied by the separately verified feasibility algorithm. -/
namespace BuyAtBulk.PolynomialLP
open RationalLP Computation.Rational
open scoped BigOperators
variable {J : Type} [Fintype J] [DecidableEq J]

theorem absolute_of_bits (q : ℚ) (L : ℕ) (bits : (Code.ofRat q).bits ≤ L) :
    |q| < (2 : ℚ)^(L+1) := by
  have bound := Code.bounded_mono (Code.ofRat q).bounded_of_bits (Nat.add_le_add_right bits 1)
  have numerator : (q.num.natAbs : ℚ) < (2 : ℚ)^(L+1) := by exact_mod_cast bound.1
  have abs_eq : (q.num.natAbs : ℚ) = |(q.num : ℚ)| := by
    simpa only [Int.cast_natCast] using
      (congrArg (fun z : ℤ => (z : ℚ)) (Int.natCast_natAbs q.num)).trans (Int.cast_abs (R := ℚ))
  rw [abs_eq] at numerator
  have den_positive : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have den_one : (1 : ℚ) ≤ q.den := by exact_mod_cast q.den_pos
  rw [Rat.abs_def,Rat.divInt_eq_div]
  push_cast
  apply (div_lt_iff₀ den_positive).mpr
  exact numerator.trans_le (by nlinarith)

def searchMagnitude (dimension coefficientBits : ℕ) : ℚ := (2 : ℚ)^(coefficientBits+dimension+2)

def searchBracket (dimension coefficientBits : ℕ) : Bracket :=
  ⟨-searchMagnitude dimension coefficientBits,searchMagnitude dimension coefficientBits⟩

theorem objective_bracket (form : (J → ℚ) →ₗ[ℚ] ℚ) (x : J → ℚ) (L : ℕ)
    (coefficients : ∀ j, (Code.ofRat (form (Pi.single j 1))).bits ≤ L)
    (cube : ∀ j, 0 ≤ x j ∧ x j ≤ 1) :
    (searchBracket (Fintype.card J) L).lower ≤ form x ∧
      form x ≤ (searchBracket (Fintype.card J) L).upper := by
  have each (j : J) : |form (Pi.single j 1)*x j| ≤ (2 : ℚ)^(L+1) := by
    rw [abs_mul,abs_of_nonneg (cube j).1]
    exact (mul_le_mul_of_nonneg_left (cube j).2 (abs_nonneg _)).trans
      (by simpa using (absolute_of_bits _ L (coefficients j)).le)
  have bound : |form x| ≤ (Fintype.card J : ℚ)*(2 : ℚ)^(L+1) := by
    rw [linearForm_expansion form x]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum fun j _ => each j).trans_eq (by simp))
  have dimension : (Fintype.card J : ℚ) ≤ (2 : ℚ)^Fintype.card J := by exact_mod_cast Nat.lt_two_pow_self.le
  have magnitude : (Fintype.card J : ℚ)*(2 : ℚ)^(L+1) ≤ searchMagnitude (Fintype.card J) L := by
    apply (mul_le_mul_of_nonneg_right dimension (by positivity)).trans
    unfold searchMagnitude
    rw [← pow_add]
    apply pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2)
    omega
  have final := bound.trans magnitude
  exact abs_le.mp final

def searchRounds (dimension coefficientBits valueBits : ℕ) : ℕ :=
  coefficientBits+dimension+2+2*(valueBits+1)+3

theorem search_precision (dimension L B : ℕ) :
    ((searchBracket dimension L).upper-(searchBracket dimension L).lower)/
      (2 : ℚ)^(searchRounds dimension L B) < 1/(2*((2 : ℚ)^(B+1))^2) := by
  have power : (2 : ℚ)^(searchRounds dimension L B) =
      8*searchMagnitude dimension L*((2 : ℚ)^(B+1))^2 := by
    unfold searchRounds searchMagnitude
    have exponent : L+dimension+2+2*(B+1)+3 = (L+dimension+2)+(B+1)+(B+1)+3 := by omega
    rw [exponent,pow_add,pow_add,pow_add]
    norm_num
    ring
  have mag_pos : 0 < searchMagnitude dimension L := by unfold searchMagnitude; positivity
  have den_pos : (0 : ℚ) < (2 : ℚ)^(B+1) := by positivity
  simp only [searchBracket,sub_neg_eq_add,power]
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [sq_pos_of_pos den_pos]

end BuyAtBulk.PolynomialLP
