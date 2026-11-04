import BuyAtBulk.Computation.PolynomialLP.Trace.Schedule
import BuyAtBulk.Computation.PolynomialLP.MatrixArithmeticBits

/-! All actual powers, counters and rational operands in normalization have
polynomial word bounds from dimension and the input's binary length. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP.Trace
open Computation Computation.Runtime Rational

def precisionWordBudget (n : ℕ) : ℕ :=
  let T := 256 * n * (n + 1)
  n + 256 + T + (T + 3) * (T + 2) + 10

theorem normalizationPrecision_words (n : ℕ) :
    WordsWithin (precisionWordBudget n) (normalizationPrecision n).events := by
  let T := 256 * n * (n + 1)
  have size : T.size ≤ T := Nat.size_le.mpr Nat.lt_two_pow_self
  have log := ceilingLog_words 2 T T
  have twoSize : Nat.size 2 = 2 := by decide
  rw [twoSize] at log
  have compare := Nat.mul_le_mul_right (T + 2) (show 2 + T.size + 1 ≤ T + 3 by omega)
  have logger := log.mono
    (show (2 + T.size + 1) * (T + 2) + 2 ≤ precisionWordBudget n by
      dsimp only [precisionWordBudget]
      change _ ≤ n + 256 + T + (T + 3) * (T + 2) + 10
      omega)
  have nSize : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have dSize : (n + 1).size ≤ n + 1 := Nat.size_le.mpr Nat.lt_two_pow_self
  have firstSize : (256 * n).size ≤ 256 * n := Nat.size_le.mpr Nat.lt_two_pow_self
  have firstBound : 256 * n ≤ T := by dsimp [T]; nlinarith
  have constant : Nat.size 256 = 9 := by decide
  simp only [normalizationPrecision, Traced.bind_events, Traced.bind_value,
    addNat_value, multiplyNat_value, wordsWithin_append]
  refine ⟨?_, ?_, ?_, logger⟩
  all_goals
    simp only [addNat, multiplyNat, emit, wordsWithin_cons, wordsWithin_nil,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true, constant]
    repeat' apply And.intro
    all_goals
      first
      | (apply (Nat.size_le.mpr Nat.lt_two_pow_self).trans
         dsimp only [precisionWordBudget]
         change _ ≤ n + 256 + T + (T + 3) * (T + 2) + 10
         omega)
      | (dsimp only [precisionWordBudget]
         change _ ≤ n + 256 + T + (T + 3) * (T + 2) + 10
         omega)

def rootFuelWordBudget (n Q : ℕ) : ℕ :=
  Q + precisionWordBudget n + 3 * (Q + 1) + 2 * n + 30

theorem rootFuel_words (q : ℚ) (n Q : ℕ) (input : (Code.ofRat q).bits ≤ Q) :
    WordsWithin (rootFuelWordBudget n Q) (rootFuel q n).events := by
  have bits := (InputTrace.codeBits_words q).mono
    (show (Code.ofRat q).bits + 2 ≤ rootFuelWordBudget n Q by dsimp [rootFuelWordBudget]; omega)
  have precision := (normalizationPrecision_words n).mono
    (show precisionWordBudget n ≤ rootFuelWordBudget n Q by dsimp [rootFuelWordBudget]; omega)
  have precisionBound := PolynomialLP.normalizationPrecision_bound n
  simp only [rootFuel, Traced.bind_events, Traced.bind_value, InputTrace.codeBits_value,
    normalizationPrecision_value, addNat_value, multiplyNat_value, wordsWithin_append]
  refine ⟨bits, precision, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [addNat, multiplyNat, emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
    repeat' apply And.intro
    all_goals
      apply (Nat.size_le.mpr Nat.lt_two_pow_self).trans
      dsimp only [rootFuelWordBudget]
      omega

def rootWordBudget (n Q : ℕ) : ℕ := rootFuelWordBudget n Q +
  (128 * ((Q + 1) + (3 * (Q + 1) + 2 * n + 12) + 2) + 256) + rootBudget n Q

theorem normalizationRoot_words (q : ℚ) (n Q : ℕ) (input : (Code.ofRat q).bits ≤ Q) :
    WordsWithin (rootWordBudget n Q) (normalizationRoot q n).events := by
  have fuel := (rootFuel_words q n Q input).mono
    (show rootFuelWordBudget n Q ≤ rootWordBudget n Q by dsimp [rootWordBudget]; omega)
  have rootInput := Code.bounded_mono (Code.bounded_of_bits (Code.ofRat q)) (Nat.add_le_add_right input 1)
  have precision := PolynomialLP.normalizationPrecision_bound n
  have bracket := (sqrtBracket_words q (rootFuel q n).value (Q + 1) rootInput).mono
    (show 128 * ((Q + 1) + (rootFuel q n).value + 2) + 256 ≤ rootWordBudget n Q by
      rw [rootFuel_value]
      dsimp only [rootWordBudget]
      omega)
  have upper := PolynomialLP.normalizationRoot_bits q n Q input
  have decoded : (sqrtBracket q (rootFuel q n).value).value.2 = PolynomialLP.normalizationRoot q n := by
    rw [rootFuel_value]
    rfl
  simp only [normalizationRoot, wordsWithin_append]
  refine ⟨⟨fuel, bracket⟩, ?_⟩
  simp only [wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq, and_true, decoded]
  dsimp only [rootWordBudget]
  omega

end BuyAtBulk.PolynomialLP.Trace
