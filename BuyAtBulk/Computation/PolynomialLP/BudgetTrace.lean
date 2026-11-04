import BuyAtBulk.Computation.PolynomialLP.InputTrace

/-! An explicit scan computes the solver's input bit budget from its actual
stored rationals. Every integer-length scan, scalar read and sum is charged. -/
namespace BuyAtBulk.PolynomialLP.InputTrace
open Computation.Runtime Computation.Rational
variable {n m : ℕ}

def vectorBudgetScan (values : Vector ℚ n) : List (Fin n) → Traced ℕ
  | [] => emit .write [0] 0
  | i :: rest => do
      let _ ← emit .scan [i.val.size] ()
      let q ← readRat values i
      let bits ← codeBits q
      let _ ← emit .recurse [rest.length.size] ()
      let tail ← vectorBudgetScan values rest
      emit .natAdd [bits.size, tail.size, (bits + tail).size] (bits + tail)

@[simp] theorem vectorBudgetScan_value (values : Vector ℚ n) (indices : List (Fin n)) :
    (vectorBudgetScan values indices).value = (indices.map fun i => (Code.ofRat values[i.val]).bits).sum := by
  induction indices with
  | nil => rfl
  | cons i rest ih => simp [vectorBudgetScan, readRat, emit, ih]

theorem vectorBudgetScan_count (values : Vector ℚ n) (indices : List (Fin n)) (L : ℕ)
    (inputs : ∀ i ∈ indices, (Code.ofRat values[i.val]).bits ≤ L) :
    (vectorBudgetScan values indices).events.length ≤ indices.length * (6 * L + 14) + 1 := by
  induction indices with
  | nil => simp [vectorBudgetScan, emit]
  | cons i rest ih =>
    have tail := ih (fun j member => inputs j (by simp [member]))
    have bitCount := codeBits_count values[i.val]
    have current := inputs i (by simp)
    simp only [vectorBudgetScan, Traced.bind_events, Traced.bind_value, emit_value,
      List.length_append, emit_length, readRat, List.length_cons]
    nlinarith

theorem vectorBudgetScan_bound (values : Vector ℚ n) (indices : List (Fin n)) (L : ℕ)
    (inputs : ∀ i ∈ indices, (Code.ofRat values[i.val]).bits ≤ L) :
    (vectorBudgetScan values indices).value ≤ indices.length * L := by
  rw [vectorBudgetScan_value]
  calc
    _ ≤ (indices.map fun _ => L).sum := List.sum_le_sum inputs
    _ = _ := by simp

theorem vectorBudgetScan_words (values : Vector ℚ n) (indices : List (Fin n)) (L : ℕ)
    (inputs : ∀ i ∈ indices, (Code.ofRat values[i.val]).bits ≤ L) :
    WordsWithin (2 * (n + indices.length + 1) * (L + 2)) (vectorBudgetScan values indices).events := by
  induction indices with
  | nil => simp [vectorBudgetScan, emit, WordsWithin]
  | cons i rest ih =>
    have current := inputs i (by simp)
    have tailInputs : ∀ j ∈ rest, (Code.ofRat values[j.val]).bits ≤ L :=
      fun j member => inputs j (by simp [member])
    have tail := ih tailInputs
    have tailBound := vectorBudgetScan_bound values rest L tailInputs
    have sumBound := vectorBudgetScan_bound values (i :: rest) L inputs
    have currentSize : (Code.ofRat values[i.val]).bits.size ≤ (Code.ofRat values[i.val]).bits :=
      Nat.size_le.mpr Nat.lt_two_pow_self
    have tailSize : (vectorBudgetScan values rest).value.size ≤ (vectorBudgetScan values rest).value :=
      Nat.size_le.mpr Nat.lt_two_pow_self
    have sumSize : ((Code.ofRat values[i.val]).bits + (vectorBudgetScan values rest).value).size ≤
        (Code.ofRat values[i.val]).bits + (vectorBudgetScan values rest).value :=
      Nat.size_le.mpr Nat.lt_two_pow_self
    have index : i.val.size ≤ n := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt i.isLt)
    have restIndex : rest.length.size ≤ rest.length := Nat.size_le.mpr Nat.lt_two_pow_self
    have codes := (codeBits_words values[i.val]).mono
      (show (Code.ofRat values[i.val]).bits + 2 ≤ 2 * (n + (rest.length + 1) + 1) * (L + 2) by nlinarith)
    simp only [vectorBudgetScan, Traced.bind_events, Traced.bind_value, emit_value,
      readRat, codeBits_value, wordsWithin_append, emit, wordsWithin_cons, wordsWithin_nil,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true, List.length_cons]
    repeat' apply And.intro
    all_goals first | exact codes | exact tail.mono (by nlinarith) | nlinarith

def vectorBudget (values : Vector ℚ n) : Traced ℕ := do
  let indices ← indexList n
  vectorBudgetScan values indices

@[simp] theorem vectorBudget_value (values : Vector ℚ n) :
    (vectorBudget values).value = ((List.finRange n).map fun i => (Code.ofRat values[i.val]).bits).sum := by
  simp [vectorBudget]

theorem vectorBudget_count (values : Vector ℚ n) (L : ℕ)
    (inputs : ∀ i : Fin n, (Code.ofRat values[i.val]).bits ≤ L) :
    (vectorBudget values).events.length ≤ n * (6 * L + 17) + 1 := by
  have count := vectorBudgetScan_count values (List.finRange n) L (fun i _ => inputs i)
  simp only [vectorBudget, Traced.bind_events, Traced.bind_value, List.length_append,
    indexList_count, indexList_value, List.length_finRange] at *
  nlinarith

theorem vectorBudget_bound (values : Vector ℚ n) (L : ℕ)
    (inputs : ∀ i : Fin n, (Code.ofRat values[i.val]).bits ≤ L) :
    (vectorBudget values).value ≤ n * L := by
  simpa only [vectorBudget, Traced.bind_value, indexList_value, List.length_finRange] using
    vectorBudgetScan_bound values (List.finRange n) L (fun i _ => inputs i)

theorem vectorBudget_words (values : Vector ℚ n) (L : ℕ)
    (inputs : ∀ i : Fin n, (Code.ofRat values[i.val]).bits ≤ L) :
    WordsWithin (4 * (n + 1) * (L + 2)) (vectorBudget values).events := by
  have scan := vectorBudgetScan_words values (List.finRange n) L (fun i _ => inputs i)
  simp only [List.length_finRange] at scan
  simp only [vectorBudget, Traced.bind_events, Traced.bind_value, indexList_value, wordsWithin_append]
  exact ⟨indexList_words n _ (by nlinarith), scan.mono (by nlinarith)⟩

def matrixBudgetScan (values : Vector (Vector ℚ n) m) : List (Fin m) → Traced ℕ
  | [] => emit .write [0] 0
  | i :: rest => do
      let _ ← emit .scan [i.val.size] ()
      let row ← emit .read [i.val.size, n.size] values[i.val]
      let bits ← vectorBudget row
      let _ ← emit .recurse [rest.length.size] ()
      let tail ← matrixBudgetScan values rest
      emit .natAdd [bits.size, tail.size, (bits + tail).size] (bits + tail)

@[simp] theorem matrixBudgetScan_value (values : Vector (Vector ℚ n) m) (indices : List (Fin m)) :
    (matrixBudgetScan values indices).value =
      (indices.flatMap fun i => (List.finRange n).map fun j => (Code.ofRat values[i.val][j.val]).bits).sum := by
  induction indices with
  | nil => rfl
  | cons i rest ih => simp [matrixBudgetScan, emit, ih]

theorem matrixBudgetScan_count (values : Vector (Vector ℚ n) m) (indices : List (Fin m)) (L : ℕ)
    (inputs : ∀ i ∈ indices, ∀ j : Fin n, (Code.ofRat values[i.val][j.val]).bits ≤ L) :
    (matrixBudgetScan values indices).events.length ≤ indices.length * (n * (6 * L + 17) + 5) + 1 := by
  induction indices with
  | nil => simp [matrixBudgetScan, emit]
  | cons i rest ih =>
    have tail := ih (fun k member => inputs k (by simp [member]))
    have current := vectorBudget_count values[i.val] L (inputs i (by simp))
    simp only [matrixBudgetScan, Traced.bind_events, Traced.bind_value, emit_value,
      List.length_append, emit_length, List.length_cons]
    nlinarith

theorem matrixBudgetScan_bound (values : Vector (Vector ℚ n) m) (indices : List (Fin m)) (L : ℕ)
    (inputs : ∀ i ∈ indices, ∀ j : Fin n, (Code.ofRat values[i.val][j.val]).bits ≤ L) :
    (matrixBudgetScan values indices).value ≤ indices.length * n * L := by
  induction indices with
  | nil => simp [matrixBudgetScan, emit]
  | cons i rest ih =>
    have tail := ih (fun k member => inputs k (by simp [member]))
    have current := vectorBudget_bound values[i.val] L (inputs i (by simp))
    simp only [matrixBudgetScan, Traced.bind_value, emit_value, List.length_cons]
    nlinarith

theorem matrixBudgetScan_words (values : Vector (Vector ℚ n) m) (indices : List (Fin m)) (L : ℕ)
    (inputs : ∀ i ∈ indices, ∀ j : Fin n, (Code.ofRat values[i.val][j.val]).bits ≤ L) :
    WordsWithin (8 * (m + n + indices.length + 1) * (n + 1) * (L + 2)) (matrixBudgetScan values indices).events := by
  induction indices with
  | nil => simp [matrixBudgetScan, emit, WordsWithin]
  | cons i rest ih =>
    have current := inputs i (by simp)
    have tailInputs : ∀ k ∈ rest, ∀ j : Fin n, (Code.ofRat values[k.val][j.val]).bits ≤ L :=
      fun k member => inputs k (by simp [member])
    have tail := ih tailInputs
    have tailBound := matrixBudgetScan_bound values rest L tailInputs
    have currentBound := vectorBudget_bound values[i.val] L current
    have currentSize : (vectorBudget values[i.val]).value.size ≤ (vectorBudget values[i.val]).value :=
      Nat.size_le.mpr Nat.lt_two_pow_self
    have tailSize : (matrixBudgetScan values rest).value.size ≤ (matrixBudgetScan values rest).value :=
      Nat.size_le.mpr Nat.lt_two_pow_self
    have sumSize : ((vectorBudget values[i.val]).value + (matrixBudgetScan values rest).value).size ≤
        (vectorBudget values[i.val]).value + (matrixBudgetScan values rest).value :=
      Nat.size_le.mpr Nat.lt_two_pow_self
    have index : i.val.size ≤ m := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt i.isLt)
    have restIndex : rest.length.size ≤ rest.length := Nat.size_le.mpr Nat.lt_two_pow_self
    have dimSize : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
    have row := (vectorBudget_words values[i.val] L current).mono
      (show 4 * (n + 1) * (L + 2) ≤ 8 * (m + n + (rest.length + 1) + 1) * (n + 1) * (L + 2) by nlinarith)
    simp only [matrixBudgetScan, Traced.bind_events, Traced.bind_value, emit_value,
      wordsWithin_append, emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true, List.length_cons]
    repeat' apply And.intro
    all_goals first | exact row | exact tail.mono (by nlinarith) | nlinarith

def inputBudgetTrace (input : Stored (n := n) (m := m)) : Traced ℕ := do
  let bounds ← vectorBudget input.bounds
  let indices ← indexList m
  let coefficients ← matrixBudgetScan input.coefficients indices
  let objective ← vectorBudget input.objective
  let first ← emit .natAdd [1, bounds.size, (1 + bounds).size] (1 + bounds)
  let second ← emit .natAdd [first.size, coefficients.size, (first + coefficients).size] (first + coefficients)
  emit .natAdd [second.size, objective.size, (second + objective).size] (second + objective)

@[simp] theorem inputBudgetTrace_value (input : Stored (n := n) (m := m)) :
    (inputBudgetTrace input).value = inputBudget input := by
  simp [inputBudgetTrace, inputBudget]

theorem inputBudgetTrace_count (input : Stored (n := n) (m := m)) (L : ℕ)
    (bounds : ∀ i : Fin m, (Code.ofRat input.bounds[i.val]).bits ≤ L)
    (coefficients : ∀ i : Fin m, ∀ j : Fin n, (Code.ofRat input.coefficients[i.val][j.val]).bits ≤ L)
    (objective : ∀ j : Fin n, (Code.ofRat input.objective[j.val]).bits ≤ L) :
    (inputBudgetTrace input).events.length ≤ (m * n + m + n + 1) * (6 * L + 30) + 10 := by
  have bc := vectorBudget_count input.bounds L bounds
  have cc := matrixBudgetScan_count input.coefficients (List.finRange m) L (fun i _ => coefficients i)
  have oc := vectorBudget_count input.objective L objective
  simp only [List.length_finRange] at cc
  simp only [inputBudgetTrace, Traced.bind_events, Traced.bind_value, emit_value,
    List.length_append, emit_length, indexList_count, indexList_value]
  nlinarith

theorem inputBudgetTrace_words (input : Stored (n := n) (m := m)) (L : ℕ)
    (bounds : ∀ i : Fin m, (Code.ofRat input.bounds[i.val]).bits ≤ L)
    (coefficients : ∀ i : Fin m, ∀ j : Fin n, (Code.ofRat input.coefficients[i.val][j.val]).bits ≤ L)
    (objective : ∀ j : Fin n, (Code.ofRat input.objective[j.val]).bits ≤ L) :
    WordsWithin (64 * (m + n + 1) * (n + 1) * (L + 2) + 64) (inputBudgetTrace input).events := by
  let K := 64 * (m + n + 1) * (n + 1) * (L + 2) + 64
  have bv := vectorBudget_bound input.bounds L bounds
  have cv := matrixBudgetScan_bound input.coefficients (List.finRange m) L (fun i _ => coefficients i)
  have ov := vectorBudget_bound input.objective L objective
  simp only [List.length_finRange] at cv
  have bw := (vectorBudget_words input.bounds L bounds).mono
    (show 4 * (m + 1) * (L + 2) ≤ K by dsimp [K]; nlinarith)
  have cw := (matrixBudgetScan_words input.coefficients (List.finRange m) L (fun i _ => coefficients i)).mono
    (show 8 * (m + n + (List.finRange m).length + 1) * (n + 1) * (L + 2) ≤ K by
      simp only [List.length_finRange]; dsimp [K]; nlinarith)
  have ow := (vectorBudget_words input.objective L objective).mono
    (show 4 * (n + 1) * (L + 2) ≤ K by dsimp [K]; nlinarith)
  have indices := indexList_words m K (by dsimp [K]; nlinarith)
  have sb : (vectorBudget input.bounds).value.size ≤ (vectorBudget input.bounds).value := Nat.size_le.mpr Nat.lt_two_pow_self
  have sc : (matrixBudgetScan input.coefficients (List.finRange m)).value.size ≤
      (matrixBudgetScan input.coefficients (List.finRange m)).value := Nat.size_le.mpr Nat.lt_two_pow_self
  have so : (vectorBudget input.objective).value.size ≤ (vectorBudget input.objective).value := Nat.size_le.mpr Nat.lt_two_pow_self
  have sf : (1 + (vectorBudget input.bounds).value).size ≤ 1 + (vectorBudget input.bounds).value := Nat.size_le.mpr Nat.lt_two_pow_self
  have ss : (1 + (vectorBudget input.bounds).value + (matrixBudgetScan input.coefficients (List.finRange m)).value).size ≤
      1 + (vectorBudget input.bounds).value + (matrixBudgetScan input.coefficients (List.finRange m)).value := Nat.size_le.mpr Nat.lt_two_pow_self
  have st : (1 + (vectorBudget input.bounds).value + (matrixBudgetScan input.coefficients (List.finRange m)).value + (vectorBudget input.objective).value).size ≤
      1 + (vectorBudget input.bounds).value + (matrixBudgetScan input.coefficients (List.finRange m)).value + (vectorBudget input.objective).value := Nat.size_le.mpr Nat.lt_two_pow_self
  change WordsWithin K _
  simp only [inputBudgetTrace, Traced.bind_events, Traced.bind_value, emit_value, indexList_value,
    wordsWithin_append, emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
  repeat' apply And.intro
  all_goals first | exact bw | exact cw | exact ow | exact indices | (dsimp [K]; nlinarith)

theorem inputBudget_objective_bits (input : Stored (n := n) (m := m)) (j : Fin n) :
    (Code.ofRat input.objective[j.val]).bits ≤ inputBudget input := by
  have single := List.single_le_sum (fun x _ => Nat.zero_le x) (Code.ofRat input.objective[j.val]).bits
    (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩ :
      (Code.ofRat input.objective[j.val]).bits ∈
        (List.finRange n).map fun k => (Code.ofRat input.objective[k.val]).bits)
  unfold inputBudget
  omega

/-- All bounds here are derived from the stored input itself. -/
theorem inputBudgetTrace_runtime (input : Stored (n := n) (m := m)) :
    (inputBudgetTrace input).value = inputBudget input ∧
    (inputBudgetTrace input).events.length ≤
      (m * n + m + n + 1) * (6 * (2 * inputBudget input + 2) + 30) + 10 ∧
    WordsWithin (64 * (m + n + 1) * (n + 1) * (2 * inputBudget input + 4) + 64)
      (inputBudgetTrace input).events := by
  have bounds : ∀ i : Fin m, (Code.ofRat input.bounds[i.val]).bits ≤ 2 * inputBudget input + 2 :=
    fun i => Code.bounded_bits (inputBudget_bound input i)
  have coefficients : ∀ i : Fin m, ∀ j : Fin n,
      (Code.ofRat input.coefficients[i.val][j.val]).bits ≤ 2 * inputBudget input + 2 :=
    fun i j => Code.bounded_bits (inputBudget_coefficient input i j)
  have objective : ∀ j : Fin n, (Code.ofRat input.objective[j.val]).bits ≤ 2 * inputBudget input + 2 := by
    intro j
    have bound := inputBudget_objective_bits input j
    omega
  exact ⟨inputBudgetTrace_value input, inputBudgetTrace_count input _ bounds coefficients objective,
    inputBudgetTrace_words input _ bounds coefficients objective⟩

end BuyAtBulk.PolynomialLP.InputTrace
