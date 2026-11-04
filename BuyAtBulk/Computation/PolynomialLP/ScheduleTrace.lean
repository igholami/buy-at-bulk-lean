import BuyAtBulk.Computation.PolynomialLP.FeasibilityPrecision
import BuyAtBulk.Computation.PolynomialLP.Precision
import BuyAtBulk.Computation.Runtime.Numerical

/-! The exact feasibility fuel, dyadic slack and work precision are computed
by a fixed arithmetic program and an explicitly charged doubling loop. -/
set_option maxHeartbeats 3000000
namespace BuyAtBulk.PolynomialLP.InputTrace
open Computation.Runtime Computation.Rational

def addNat (a b : ℕ) : Traced ℕ := emit .natAdd [a.size, b.size, (a + b).size] (a + b)
def mulNat (a b : ℕ) : Traced ℕ := emit .natMul [a.size, b.size, (a * b).size] (a * b)
@[simp] theorem addNat_value (a b : ℕ) : (addNat a b).value = a + b := rfl
@[simp] theorem mulNat_value (a b : ℕ) : (mulNat a b).value = a * b := rfl
@[simp] theorem addNat_count (a b : ℕ) : (addNat a b).events.length = 1 := rfl
@[simp] theorem mulNat_count (a b : ℕ) : (mulNat a b).events.length = 1 := rfl

structure FeasibilitySchedule where
  slackExponent : ℕ
  interiorExponent : ℕ
  rounds : ℕ
  precision : ℕ
  slack : ℚ

def scheduleTrace (n L : ℕ) : Traced FeasibilitySchedule := do
  let d ← addNat n 1
  let dSquare ← mulNat d d
  let dL ← mulNat d L
  let gapSum ← addNat dSquare dL
  let gapOne ← addNat gapSum 1
  let gapTwice ← mulNat 2 gapOne
  let gap ← addNat gapTwice 3
  let slackN ← addNat gap n
  let slack ← addNat slackN 4
  let interiorL ← addNat slack L
  let interiorN ← addNat interiorL n
  let interior ← addNat interiorN 1
  let nSquare ← mulNat n n
  let twiceN ← mulNat 2 n
  let twiceNK ← mulNat twiceN interior
  let detSum ← addNat nSquare twiceNK
  let detOne ← addNat detSum 1
  let fourD ← mulNat 4 d
  let rounds ← mulNat fourD detOne
  let roundsOne ← addNat rounds 1
  let scaledSquare ← mulNat 64 dSquare
  let precision ← mulNat scaledSquare roundsOne
  let denominator ← powerTwo slack
  let denominatorQ ← ratCast denominator
  let epsilon ← ratDiv 1 denominatorQ
  emit .cons [slack.size, interior.size, rounds.size, precision.size, (Code.ofRat epsilon).bits]
    ⟨slack, interior, rounds, precision, epsilon⟩

theorem scheduleTrace_value (n L : ℕ) : (scheduleTrace n L).value =
    ⟨slackBits n L, interiorBits n L, feasibilityRounds n L,
      workPrecision n (feasibilityRounds n L), feasibilitySlack n L⟩ := by
  simp only [scheduleTrace, Traced.bind_value, addNat_value, mulNat_value, powerTwo_value,
    ratCast, emit_value, ratDiv_value]
  simp only [slackBits, phaseGapBits, interiorBits, feasibilityRounds, stoppingRounds,
    workPrecision, feasibilitySlack, pow_two, Nat.cast_pow, Nat.cast_ofNat]

theorem scheduleTrace_count (n L : ℕ) :
    (scheduleTrace n L).events.length = 2 * slackBits n L + 27 := by
  simp only [scheduleTrace, Traced.bind_events, Traced.bind_value, addNat_value, mulNat_value,
    List.length_append, addNat_count, mulNat_count, powerTwo_count, ratCast, emit_length,
    ratDiv_length, emit_value, powerTwo_value]
  simp only [slackBits, phaseGapBits, pow_two]
  omega

/-- A fixed sum of polynomial scalar expressions. It bounds the arithmetic
words, not the numerical value of the exponentially large dyadic denominator. -/
def scheduleValues (n L : ℕ) : List ℕ :=
  let d := n + 1
  let gapSum := d * d + d * L
  let gapOne := gapSum + 1
  let gapTwice := 2 * gapOne
  let gap := gapTwice + 3
  let slackN := gap + n
  let slack := slackN + 4
  let interiorL := slack + L
  let interiorN := interiorL + n
  let interior := interiorN + 1
  let nSquare := n * n
  let twiceN := 2 * n
  let twiceNK := twiceN * interior
  let detSum := nSquare + twiceNK
  let detOne := detSum + 1
  let fourD := 4 * d
  let rounds := fourD * detOne
  let roundsOne := rounds + 1
  let scaledSquare := 64 * (d * d)
  let precision := scaledSquare * roundsOne
  [n, L, 1, 2, 3, 4, 64, d, d * d, d * L, gapSum, gapOne, gapTwice, gap,
    slackN, slack, interiorL, interiorN, interior, nSquare, twiceN, twiceNK,
    detSum, detOne, fourD, rounds, roundsOne, scaledSquare, precision]

def scheduleWordBudget (n L : ℕ) : ℕ := 8 * ((scheduleValues n L).sum + 32)

theorem scheduleTrace_words (n L : ℕ) :
    WordsWithin (scheduleWordBudget n L) (scheduleTrace n L).events := by
  let p := slackBits n L
  have pBound : p ≤ (scheduleValues n L).sum := by
    unfold p slackBits phaseGapBits scheduleValues
    simp only [pow_two, List.sum_cons, List.sum_nil]
    omega
  have powerWords := (powerTwo_words p).mono
    (show p + 2 ≤ scheduleWordBudget n L by unfold scheduleWordBudget; omega)
  have denominatorBits : (Code.ofRat ((2 ^ p : ℕ) : ℚ)).bits = p + 4 := by
    simp [Code.ofRat, Code.bits, Nat.size_pow]
  have oneBits : (Code.ofRat 1).bits = 4 := by decide
  have divisionWords := WordsWithin.mono (ratDiv_words 1 ((2 ^ p : ℕ) : ℚ))
    (show 2 * ((Code.ofRat 1).bits + (Code.ofRat ((2 ^ p : ℕ) : ℚ)).bits) + 8 ≤
      scheduleWordBudget n L by rw [denominatorBits, oneBits]; unfold scheduleWordBudget; omega)
  have epsilonBits := ratDiv_result_bits 1 ((2 ^ p : ℕ) : ℚ)
  rw [denominatorBits, oneBits] at epsilonBits
  have epsilonBound : (Code.ofRat (1 / ((2 ^ p : ℕ) : ℚ))).bits ≤ scheduleWordBudget n L := by
    unfold scheduleWordBudget
    omega
  simp only [p, slackBits, phaseGapBits, pow_two] at powerWords divisionWords epsilonBound
  change WordsWithin _ _
  simp only [scheduleTrace, Traced.bind_events, Traced.bind_value, addNat_value, mulNat_value,
    powerTwo_value, ratDiv_value, ratCast, emit_value, wordsWithin_append]
  change WordsWithin _ _ ∧ _
  simp only [addNat, mulNat, emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
  repeat' apply And.intro
  all_goals first
    | exact powerWords
    | exact divisionWords
    | exact epsilonBound
    | (try simp only [Nat.size_pow]
       first
       | (apply (Nat.size_le.mpr Nat.lt_two_pow_self).trans
          unfold scheduleWordBudget scheduleValues
          simp only [List.sum_cons, List.sum_nil]
          omega)
       | (unfold scheduleWordBudget scheduleValues
          simp only [List.sum_cons, List.sum_nil]
          omega))

end BuyAtBulk.PolynomialLP.InputTrace
