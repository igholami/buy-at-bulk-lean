import BuyAtBulk.Computation.PolynomialLP.IntegerizationWords
import BuyAtBulk.Computation.PolynomialLP.BoxWords
import BuyAtBulk.Computation.PolynomialLP.ScheduleTrace

/-! The complete stored-input preparation for the actual rounded ellipsoid
loop, including source-derived encoding budgets and dyadic slack. -/
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP.InputTrace
open Computation.Runtime Computation.Rational
variable {n m : ℕ}

structure Prepared (n m : ℕ) where
  input : Stored (n := n) (m := m + (n + n))
  schedule : FeasibilitySchedule
  integerBits : ℕ

def prepareTrace (input : Stored (n := n) (m := m)) : Traced (Prepared n m) :=
  let budget := inputBudgetTrace input
  let nTwo := addNat n 2
  let L := mulNat nTwo.value budget.value
  let table := integerizeTrace input
  let boxed := boxedTrace table.value
  let schedule := scheduleTrace n L.value
  let relaxed := slackTrace boxed.value schedule.value.slack
  ⟨⟨relaxed.value, schedule.value, L.value⟩,
    budget.events ++ nTwo.events ++ L.events ++ table.events ++ boxed.events ++
      schedule.events ++ relaxed.events ++
        [⟨.cons, [n.size, m.size, schedule.value.rounds.size, schedule.value.precision.size]⟩]⟩

theorem prepareTrace_value (input : Stored (n := n) (m := m)) :
    (prepareTrace input).value =
      ⟨(integerize input).boxed.slack (feasibilitySlack n (integerL input)),
        ⟨slackBits n (integerL input), interiorBits n (integerL input),
          feasibilityRounds n (integerL input), workPrecision n (feasibilityRounds n (integerL input)),
          feasibilitySlack n (integerL input)⟩, integerL input⟩ := by
  simp only [prepareTrace, Traced.bind_value, inputBudgetTrace_value, addNat_value,
    mulNat_value, integerizeTrace_value, boxedTrace_value, scheduleTrace_value,
    slackTrace_value, emit_value, integerL]

def preparationCount (n m B : ℕ) : ℕ :=
  ((m * n + m + n + 1) * (6 * (2 * B + 2) + 30) + 10) + 2 +
    (m * (21 * n + 22) + 5) + (10 * n * n + 42 * n + 6 * m + 10) +
    (2 * slackBits n ((n + 2) * B) + 27) + (5 * (m + (n + n)) + 4) + 1

theorem prepareTrace_count (input : Stored (n := n) (m := m)) :
    (prepareTrace input).events.length ≤ preparationCount n m (inputBudget input) := by
  have budget := (inputBudgetTrace_runtime input).2.1
  have integerized := integerizeTrace_count input
  have boxed := boxedTrace_count (integerize input)
  have slack := slackTrace_count (integerize input).boxed (feasibilitySlack n (integerL input))
  simp only [prepareTrace, Traced.bind_events, Traced.bind_value, inputBudgetTrace_value,
    addNat_value, mulNat_value, integerizeTrace_value, boxedTrace_value, scheduleTrace_value,
    slackTrace_value, emit_value, List.length_append, addNat_count, mulNat_count, scheduleTrace_count,
    emit_length, List.length_cons, List.length_nil]
  dsimp only [preparationCount]
  simp only [integerL] at slack
  omega

theorem dyadicReciprocal_bits (p : ℕ) : (Code.ofRat (1 / (2 : ℚ) ^ p)).bits ≤ p + 4 := by
  let code : Code := ⟨1, (2 : ℤ) ^ p, pow_ne_zero _ (by decide)⟩
  have decoded : code.value = 1 / (2 : ℚ) ^ p := by simp [code, Code.value]
  rw [← decoded]
  have bound := Code.normalized_bits_le code
  have raw : code.bits = p + 4 := by
    simp [code, Code.bits, Int.natAbs_pow, Nat.size_pow] <;> omega
  exact bound.trans_eq raw

theorem integerized_boxed_bits (input : Stored (n := n) (m := m)) :
    (∀ i : Fin (m + (n + n)), ∀ j : Fin n,
      (Code.ofRat (integerize input).boxed.coefficients[i.val][j.val]).bits ≤ integerL input + 4) ∧
    (∀ i : Fin (m + (n + n)),
      (Code.ofRat (integerize input).boxed.bounds[i.val]).bits ≤ integerL input + 4) := by
  obtain ⟨coefficients, bounds, ab, bb⟩ := boxed_integer_data input
  constructor
  · intro i j
    rw [coefficients, integerCast_bits]
    have size := Nat.size_le_size (ab i j)
    simp only [integerH, Nat.size_pow] at size
    omega
  · intro i
    rw [bounds, integerCast_bits]
    have size := Nat.size_le_size (bb i)
    simp only [integerH, Nat.size_pow] at size
    omega

def preparationWords (n m B : ℕ) : ℕ :=
  let L := (n + 2) * B
  (64 * (m + n + 1) * (n + 1) * (2 * B + 4) + 64) +
    integerizeWordBudget n m B + boxedWordBudget n m (L + 3) + scheduleWordBudget n L +
    (m + (n + n) + n + 2 * (L + 4 + (slackBits n L + 4)) + 10) +
    n + m + B + L + feasibilityRounds n L + workPrecision n (feasibilityRounds n L) + 10

theorem integerized_bits (input : Stored (n := n) (m := m)) :
    (∀ i : Fin m, ∀ j : Fin n,
      (Code.ofRat (integerize input).coefficients[i.val][j.val]).bits ≤ integerL input + 3) ∧
    (∀ i : Fin m, (Code.ofRat (integerize input).bounds[i.val]).bits ≤ integerL input + 3) := by
  constructor
  · intro i j
    rw [integerize_coefficient_int, integerCast_bits]
    have size := Nat.size_le.mpr (integerA_bound input i j)
    exact Nat.add_le_add_right size 3
  · intro i
    rw [integerize_bound_int, integerCast_bits]
    have size := Nat.size_le.mpr (integerB_bound input i)
    exact Nat.add_le_add_right size 3

theorem prepareTrace_words (input : Stored (n := n) (m := m)) :
    WordsWithin (preparationWords n m (inputBudget input)) (prepareTrace input).events := by
  let K := preparationWords n m (inputBudget input)
  have budget := (inputBudgetTrace_runtime input).2.2.mono
    (show _ ≤ K by dsimp only [K, preparationWords]; omega)
  have integers := (integerizeTrace_runtime input).2.2.mono
    (show _ ≤ K by dsimp only [K, preparationWords]; omega)
  have integral := integerized_bits input
  have boxed := (boxedTrace_words (integerize input) (integerL input + 3) integral.1 integral.2).mono
    (show _ ≤ K by dsimp only [K, preparationWords, integerL]; omega)
  have schedule := (scheduleTrace_words n (integerL input)).mono
    (show _ ≤ K by dsimp only [K, preparationWords, integerL]; omega)
  have epsilon : (Code.ofRat (feasibilitySlack n (integerL input))).bits ≤ slackBits n (integerL input) + 4 :=
    dyadicReciprocal_bits _
  have slack := (slackTrace_words (integerize input).boxed (feasibilitySlack n (integerL input))
    (integerL input + 4) (integerized_boxed_bits input).2).mono
    (show _ ≤ K by dsimp only [K, preparationWords]; simp only [integerL] at epsilon ⊢; omega)
  simp only [prepareTrace, Traced.bind_events, Traced.bind_value, inputBudgetTrace_value,
    addNat_value, mulNat_value, integerizeTrace_value, boxedTrace_value, scheduleTrace_value,
    slackTrace_value, emit_value, List.append_assoc, wordsWithin_append]
  refine ⟨budget, ?_, ?_, integers, boxed, schedule, slack, ?_⟩
  all_goals
    simp only [addNat, mulNat, emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
    repeat' apply And.intro
    all_goals
      apply (Nat.size_le.mpr Nat.lt_two_pow_self).trans
      dsimp only [K, preparationWords]
      omega

end BuyAtBulk.PolynomialLP.InputTrace
