import BuyAtBulk.Computation.PolynomialLP.Trace.Dyadic
import BuyAtBulk.Computation.PolynomialLP.SquareRoot

/-! All dyadic rounding dividend, quotient, raw pair and normalized values
have polynomial binary width in input length and requested precision. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP.Trace
open Computation Computation.Runtime Rational

def dyadicWordBudget (Q p : ℕ) : ℕ := 4 * (Q + p + 4) + 20

theorem dyadic_words (q : ℚ) (p Q : ℕ) (input : (Code.ofRat q).bits ≤ Q) :
    WordsWithin (dyadicWordBudget Q p) (dyadic q p).events := by
  have codeBound := Code.bounded_mono (Code.bounded_of_bits (Code.ofRat q)) (Nat.add_le_add_right input 1)
  have magnitude : |q| ≤ (2 : ℚ) ^ (Q + 1) :=
    (rational_abs_binary_bound q).trans
      (pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right input 1))
  have pairBound := dyadic_bits q p (Q + 1) magnitude
  have numeratorSize : (dyadicNumerator q p).natAbs.size ≤ 2 * (Q + 1 + p + 2) + 2 := by
    dsimp only [Code.bits, dyadicCode] at pairBound
    omega
  have dividend : (q.num * (2 : ℤ) ^ p).natAbs < 2 ^ (Q + 1 + p) := by
    rw [Int.natAbs_mul, Int.natAbs_pow]
    norm_num
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_right codeBound.1 (by positivity)
  have dividendSize := Nat.size_le.mpr dividend
  have qNum : q.num.natAbs.size ≤ Q := by
    simp only [Code.ofRat, Code.bits, Int.natAbs_natCast] at input
    omega
  have qDen : q.den.size ≤ Q := by
    simp only [Code.ofRat, Code.bits, Int.natAbs_natCast] at input
    omega
  have denSize : ((2 : ℤ) ^ p).natAbs.size = p + 1 := by simp [Int.natAbs_pow, Nat.size_pow]
  have powers := (powerTwo_words p).mono
    (show p + 2 ≤ dyadicWordBudget Q p by dsimp [dyadicWordBudget]; omega)
  have decoder := (Original.decodeRat_words (dyadicCode q p)).mono
    (show (dyadicCode q p).bits + 3 ≤ dyadicWordBudget Q p by dsimp [dyadicWordBudget]; omega)
  simp only [dyadic, powerTwo_value, Int.natCast_pow, Nat.cast_ofNat, wordsWithin_append]
  refine ⟨⟨powers, ?_⟩, decoder⟩
  simp only [wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, and_true, Nat.size_pow, denSize]
  change _ ∧ _ ∧ _ ∧ _ ∧ _
  have pairBound' : (⟨(q.num * (2 : ℤ) ^ p) / (q.den : ℤ), (2 : ℤ) ^ p,
      pow_ne_zero _ (by decide)⟩ : Code).bits ≤ 2 * (Q + 1 + p + 2) + 2 := pairBound
  have quotientSize : ((q.num * (2 : ℤ) ^ p) / (q.den : ℤ)).natAbs.size ≤
      2 * (Q + 1 + p + 2) + 2 := numeratorSize
  dsimp only [dyadicWordBudget]
  repeat' apply And.intro
  all_goals omega

theorem dyadic_result_bits (q : ℚ) (p Q : ℕ) (input : (Code.ofRat q).bits ≤ Q) :
    (Code.ofRat (dyadic q p).value).bits ≤ dyadicWordBudget Q p := by
  have magnitude : |q| ≤ (2 : ℚ) ^ (Q + 1) :=
    (rational_abs_binary_bound q).trans
      (pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right input 1))
  have raw := dyadic_bits q p (Q + 1) magnitude
  rw [dyadic_value]
  exact (Code.normalized_bits_le _).trans (raw.trans (by dsimp [dyadicWordBudget]; omega))

end BuyAtBulk.PolynomialLP.Trace
