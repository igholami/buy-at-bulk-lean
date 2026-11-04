import BuyAtBulk.Computation.PolynomialLP.Trace.LowDimension
import BuyAtBulk.Computation.PolynomialLP.Words.Separation

/-! Unary interval endpoints always come from one row quotient or an existing
endpoint, so word widths do not accumulate with the number of rows. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace BuyAtBulk.PolynomialLP.Trace
open Computation Computation.Runtime Rational
variable {m : ℕ}

def IntervalBits (interval : Interval) (B : ℕ) : Prop :=
  (Code.ofRat interval.lower).bits ≤ B ∧ (Code.ofRat interval.upper).bits ≤ B

def cutWordBudget (L : ℕ) := 4 * L + 20

theorem cut_interval_bits (interval : Interval) (a b : ℚ) (L : ℕ)
    (old : IntervalBits interval (4 * L + 8))
    (ab : (Code.ofRat a).bits ≤ L) (bb : (Code.ofRat b).bits ≤ L) :
    IntervalBits (cut interval a b).value (4 * L + 8) := by
  have division := ratDiv_result_bits b a
  have zero : (Code.ofRat 0).bits = 3 := by decide
  have one : (Code.ofRat 1).bits = 4 := by decide
  rcases old with ⟨lower, upper⟩
  simp only [cut_value, Interval.cut, IntervalBits, min_def, max_def]
  split_ifs <;> simp_all
  all_goals repeat' apply And.intro
  all_goals omega

theorem cut_words (interval : Interval) (a b : ℚ) (L : ℕ)
    (old : IntervalBits interval (4 * L + 8))
    (ab : (Code.ofRat a).bits ≤ L) (bb : (Code.ofRat b).bits ≤ L) :
    WordsWithin (cutWordBudget L) (cut interval a b).events := by
  rcases old with ⟨lower, upper⟩
  have division := ratDiv_result_bits b a
  have zero : (Code.ofRat 0).bits = 3 := by decide
  have one : (Code.ofRat 1).bits = 4 := by decide
  have rawDiv := Code.bounded_bits (Code.div_bounded
    (Code.bounded_of_bits (Code.ofRat b)) (Code.bounded_of_bits (Code.ofRat a)) (by omega))
  have divWords := WordsWithin.mono (ratDiv_words b a)
    (show _ ≤ cutWordBudget L by dsimp only [cutWordBudget]; omega)
  simp only [cut, Traced.bind_events, Traced.bind_value, emit_value, branch,
    ratDiv_value, ratLe, ratLess, decide_eq_true_eq]
  all_goals
    repeat' first
      | (simp only [Bind.bind, Traced.instMonad, Traced.bind, Traced.bind_events,
          Traced.bind_value, emit_value, branch, ratDiv_value, ratLe, ratLess, writeInterval,
          wordsWithin_append, emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons,
          List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true, decide_eq_true_eq])
      | split_ifs
      | apply And.intro
  all_goals first | exact divWords | (dsimp only [cutWordBudget]; omega)

def unaryScanWordBudget (m L : ℕ) := m + cutWordBudget L + L + 10

theorem intervalScan_bits (input : Stored (n := 1) (m := m)) (rows : List (Fin m))
    (interval : Interval) (L : ℕ)
    (coefficients : ∀ i : Fin m, (Code.ofRat input.coefficients[i.val][0]).bits ≤ L)
    (bounds : ∀ i : Fin m, (Code.ofRat input.bounds[i.val]).bits ≤ L)
    (old : IntervalBits interval (4 * L + 8)) :
    IntervalBits (intervalScan input rows interval).value (4 * L + 8) := by
  induction rows generalizing interval with
  | nil => exact old
  | cons i rest ih =>
    have next := cut_interval_bits interval input.coefficients[i.val][0] input.bounds[i.val] L old (coefficients i) (bounds i)
    simp only [cut_value] at next
    have recursive := ih (interval.cut input.coefficients[i.val][0] input.bounds[i.val]) next
    simpa only [intervalScan, Traced.bind_value, emit_value, readRat, cut_value, Fin.val_zero] using recursive

theorem intervalScan_words (input : Stored (n := 1) (m := m)) (rows : List (Fin m))
    (interval : Interval) (L : ℕ)
    (coefficients : ∀ i : Fin m, (Code.ofRat input.coefficients[i.val][0]).bits ≤ L)
    (bounds : ∀ i : Fin m, (Code.ofRat input.bounds[i.val]).bits ≤ L)
    (old : IntervalBits interval (4 * L + 8)) :
    WordsWithin (unaryScanWordBudget m L) (intervalScan input rows interval).events := by
  induction rows generalizing interval with
  | nil => exact wordsWithin_nil _
  | cons i rest ih =>
    have index : i.val.size ≤ m := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt i.isLt)
    have coefficient := coefficients i
    have bound := bounds i
    have next := cut_interval_bits interval input.coefficients[i.val][0] input.bounds[i.val] L old coefficient bound
    simp only [cut_value] at next
    have row := (cut_words interval input.coefficients[i.val][0] input.bounds[i.val] L old coefficient bound).mono
      (show _ ≤ unaryScanWordBudget m L by dsimp only [unaryScanWordBudget]; omega)
    have recursive := ih (interval.cut input.coefficients[i.val][0] input.bounds[i.val]) next
    simp only [intervalScan, Traced.bind_events, Traced.bind_value, emit_value,
      readRat, cut_value, Fin.val_zero, wordsWithin_append]
    refine ⟨?_, ?_, ?_, ?_, row, recursive⟩
    all_goals
      simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, forall_eq, and_true, Nat.size_zero]
      dsimp only [unaryScanWordBudget]
      repeat' apply And.intro
      all_goals omega

def unaryWordBudget (m L : ℕ) := unaryScanWordBudget m L + m + 8 * L + 100

theorem unarySolve_words (input : Stored (n := 1) (m := m)) (L : ℕ)
    (coefficients : ∀ i : Fin m, (Code.ofRat input.coefficients[i.val][0]).bits ≤ L)
    (bounds : ∀ i : Fin m, (Code.ofRat input.bounds[i.val]).bits ≤ L)
    (objective : (Code.ofRat input.objective[0]).bits ≤ L) :
    WordsWithin (unaryWordBudget m L) (unarySolve input).events := by
  let K := unaryWordBudget m L
  let interval := (intervalScan input (List.finRange m) ⟨0, 1⟩).value
  have zero : (Code.ofRat 0).bits = 3 := by decide
  have one : (Code.ofRat 1).bits = 4 := by decide
  have initial : IntervalBits ⟨0, 1⟩ (4 * L + 8) := by
    dsimp only [IntervalBits]
    constructor <;> omega
  have scanned := intervalScan_bits input (List.finRange m) ⟨0, 1⟩ L coefficients bounds initial
  have lower : (Code.ofRat interval.lower).bits ≤ 4 * L + 8 := scanned.1
  have upper : (Code.ofRat interval.upper).bits ≤ 4 * L + 8 := scanned.2
  have scanWords := (intervalScan_words input (List.finRange m) ⟨0, 1⟩ L coefficients bounds initial).mono
    (show _ ≤ K by dsimp only [K, unaryWordBudget]; omega)
  have indices := indexList_words m K (by dsimp only [K, unaryWordBudget]; omega)
  have compare : WordsWithin K (ratLe interval.lower interval.upper).events := by
    simp only [ratLe, emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, and_true]
    dsimp only [K, unaryWordBudget]
    constructor <;> omega
  have tag {α : Type} (value : α) : WordsWithin K (emit .branch [1] value).events := by
    simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq, and_true]
    dsimp only [K, unaryWordBudget]
    omega
  have read : WordsWithin K (readRat input.objective 0).events := by
    simp only [readRat, emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, and_true, Fin.val_zero, Nat.size_zero]
    dsimp only [K, unaryWordBudget]
    constructor <;> omega
  have negative : WordsWithin K (ratLess input.objective[0] 0).events := by
    simp only [ratLess, emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, and_true]
    dsimp only [K, unaryWordBudget]
    constructor <;> omega
  have endpoint : (Code.ofRat (if input.objective[0] < 0 then interval.upper else interval.lower)).bits ≤ 4 * L + 8 := by
    split_ifs <;> omega
  dsimp only [interval] at lower upper endpoint
  simp only [unarySolve, Traced.bind_events, Traced.bind_value, indexList_value,
    ratLe, emit_value, branch, wordsWithin_append]
  refine ⟨indices, scanWords, compare, tag _, ?_⟩
  by_cases valid : interval.lower ≤ interval.upper
  · dsimp only [interval] at valid
    simp only [valid, decide_true, Bool.true_eq, ite_true, Traced.bind_events, Traced.bind_value,
      readRat, emit_value, ratLess, branch, decide_eq_true_eq, wordsWithin_append, Fin.val_zero]
    refine ⟨read, negative, tag _, ?_⟩
    simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, and_true]
    dsimp only [K, unaryWordBudget]
    constructor <;> omega
  · dsimp only [interval] at valid
    simp only [valid, decide_false, Bool.false_eq_true, ite_false, emit, wordsWithin_cons,
      wordsWithin_nil, List.mem_cons, List.not_mem_nil, or_false, forall_eq, and_true]
    dsimp only [K, unaryWordBudget]
    omega

def zeroWordBudget (m L : ℕ) := separationWordBudget 0 m (L + 5) + m + 10

theorem zeroSolve_words (input : Stored (n := 0) (m := m)) (L : ℕ)
    (bounds : ∀ i : Fin m, (Code.ofRat input.bounds[i.val]).bits ≤ L) :
    WordsWithin (zeroWordBudget m L) (zeroSolve input).events := by
  have separation := (separate_words input (Vector.replicate 0 0) (L + 5) (by omega)
    (by intro i j; exact j.elim0) (by intro i; have bound := bounds i; omega)
    (by intro j; exact j.elim0)).mono
      (show _ ≤ zeroWordBudget m L by dsimp only [zeroWordBudget]; omega)
  simp only [zeroSolve, Traced.bind_events, Traced.bind_value, emit_value, wordsWithin_append]
  refine ⟨?_, separation, ?_, ?_⟩
  all_goals
    simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq, and_true]
    dsimp only [zeroWordBudget]
    omega

end BuyAtBulk.PolynomialLP.Trace
