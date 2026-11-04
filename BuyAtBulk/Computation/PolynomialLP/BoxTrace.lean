import BuyAtBulk.Computation.PolynomialLP.CutData
import BuyAtBulk.Computation.PolynomialLP.SlackData
import BuyAtBulk.Computation.Runtime.Weights

/-! Actual box-row construction, array concatenation and rational slack
updates, with every materialized cell read/written in the closed trace. -/
namespace BuyAtBulk.PolynomialLP.InputTrace
open Computation.Runtime Computation.Rational
variable {n m k : ℕ} {α : Type}

def appendVector (left : Vector α m) (right : Vector α k) (width : α → ℕ) : Traced (Vector α (m + k)) :=
  ⟨left ++ right,
    [⟨.write, [(m + k).size]⟩] ++
    (List.finRange m).flatMap (fun i =>
      [⟨.scan, [i.val.size]⟩, ⟨.read, [i.val.size, width left[i.val]]⟩,
       ⟨.write, [i.val.size, width left[i.val]]⟩]) ++
    (List.finRange k).flatMap (fun j =>
      [⟨.scan, [j.val.size]⟩, ⟨.read, [j.val.size, width right[j.val]]⟩,
       ⟨.natAdd, [m.size, j.val.size, (m + j.val).size]⟩,
       ⟨.write, [(m + j.val).size, width right[j.val]]⟩])⟩

@[simp] theorem appendVector_value (left : Vector α m) (right : Vector α k) (width : α → ℕ) :
    (appendVector left right width).value = left ++ right := rfl

theorem appendVector_count (left : Vector α m) (right : Vector α k) (width : α → ℕ) :
    (appendVector left right width).events.length = 3 * m + 4 * k + 1 := by
  simp [appendVector, List.length_flatMap]
  omega

theorem appendVector_words (left : Vector α m) (right : Vector α k) (width : α → ℕ)
    (K : ℕ) (dimensions : m + k ≤ K)
    (leftWords : ∀ i : Fin m, width left[i.val] ≤ K)
    (rightWords : ∀ j : Fin k, width right[j.val] ≤ K) :
    WordsWithin K (appendVector left right width).events := by
  have whole : (m + k).size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans dimensions
  have mi : m.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  simp only [appendVector, wordsWithin_append, wordsWithin_cons, wordsWithin_nil,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq, and_true]
  refine ⟨⟨by exact whole, ?_⟩, ?_⟩
  · intro event member word present
    obtain ⟨i, _, member⟩ := List.mem_flatMap.mp member
    have index : i.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := i.isLt; omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    all_goals rcases present with rfl | rfl
    all_goals first | exact index | exact leftWords i
  · intro event member word present
    obtain ⟨j, _, member⟩ := List.mem_flatMap.mp member
    have index : j.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := j.isLt; omega)
    have shifted : (m + j.val).size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := j.isLt; omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    all_goals first
      | (rcases present with rfl | rfl | rfl; all_goals first | exact mi | exact index | exact shifted)
      | (rcases present with rfl | rfl; all_goals first | exact index | exact shifted | exact rightWords j)
      | exact index

def coordinateCell (sign : ℚ) (i j : Fin n) : Traced ℚ := do
  let test ← emit .natCompare [i.val.size, j.val.size] (decide (i = j))
  let test ← branch test
  emit .write [(Code.ofRat (if test then sign else 0)).bits] (if test then sign else 0)

@[simp] theorem coordinateCell_value (sign : ℚ) (i j : Fin n) :
    (coordinateCell sign i j).value = if i = j then sign else 0 := by
  simp [coordinateCell, branch]

theorem conditional_bits (sign : ℚ) (test : Prop) [Decidable test] (L : ℕ)
    (input : (Code.ofRat sign).bits ≤ L) :
    (Code.ofRat (if test then sign else 0)).bits ≤ L + 3 := by
  have zero : (Code.ofRat 0).bits = 3 := by decide
  split_ifs <;> omega

theorem coordinateCell_words (sign : ℚ) (i j : Fin n) (L : ℕ)
    (input : (Code.ofRat sign).bits ≤ L) :
    WordsWithin (n + L + 3) (coordinateCell sign i j).events := by
  have ii : i.val.size ≤ n := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt i.isLt)
  have ji : j.val.size ≤ n := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt j.isLt)
  have result := conditional_bits sign (i = j) L input
  simp only [coordinateCell, Traced.bind_events, Traced.bind_value, emit_value, branch,
    wordsWithin_append, emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true, decide_eq_true_eq]
  repeat' apply And.intro
  all_goals omega

def coordinateRowsTrace (n : ℕ) (sign : ℚ) : Traced (Vector (Vector ℚ n) n) :=
  Weights.materialize (fun i : Fin n =>
    Weights.materialize (coordinateCell sign i) (fun q : ℚ => (Code.ofRat q).bits))
    (fun row : Vector ℚ n => ((List.finRange n).map fun j => (Code.ofRat row[j.val]).bits).sum)

@[simp] theorem coordinateRowsTrace_value (n : ℕ) (sign : ℚ) :
    (coordinateRowsTrace n sign).value = coordinateRows n sign := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [coordinateRowsTrace, coordinateCell, Weights.materialize, coordinateRows, branch]

theorem coordinateRowsTrace_count (n : ℕ) (sign : ℚ) :
    (coordinateRowsTrace n sign).events.length ≤ 5 * n * n + 3 * n + 1 := by
  have inner (i : Fin n) : (Weights.materialize (fun j : Fin n => do
      let test ← emit .natCompare [i.val.size, j.val.size] (decide (i = j))
      let test ← branch test
      emit .write [(Code.ofRat (if test then sign else 0)).bits] (if test then sign else 0))
      (fun q : ℚ => (Code.ofRat q).bits)).events.length ≤ 5 * n + 1 := by
    have bound := Weights.materialize_count (fun j : Fin n => do
      let test ← emit .natCompare [i.val.size, j.val.size] (decide (i = j))
      let test ← branch test
      emit .write [(Code.ofRat (if test then sign else 0)).bits] (if test then sign else 0))
      (fun q : ℚ => (Code.ofRat q).bits) 3 (by intro j; exact le_rfl)
    simpa only [Nat.reduceAdd, Nat.mul_comm] using bound
  have outer := Weights.materialize_count _
    (fun row : Vector ℚ n => ((List.finRange n).map fun j => (Code.ofRat row[j.val]).bits).sum)
    (5 * n + 1) inner
  change _ ≤ _ at outer
  change (coordinateRowsTrace n sign).events.length ≤ _ at outer
  nlinarith

theorem coordinateRowsTrace_words (n : ℕ) (sign : ℚ) (L : ℕ)
    (input : (Code.ofRat sign).bits ≤ L) :
    WordsWithin (n + n * (L + 3) + L + 10) (coordinateRowsTrace n sign).events := by
  let K := n + n * (L + 3) + L + 10
  have rowWords (i : Fin n) : WordsWithin K (Weights.materialize (coordinateCell sign i)
      (fun q : ℚ => (Code.ofRat q).bits)).events := by
    apply Weights.materialize_words
    · omega
    · intro j
      exact (coordinateCell_words sign i j L input).mono (by dsimp [K]; omega)
    · intro j
      have bit := conditional_bits sign (i = j) L input
      simp only [coordinateCell_value]
      dsimp [K]
      omega
  apply Weights.materialize_words
  · omega
  · exact rowWords
  · intro i
    have width : ((List.finRange n).map fun j => (Code.ofRat
        (Weights.materialize (coordinateCell sign i) (fun q : ℚ => (Code.ofRat q).bits)).value[j.val]).bits).sum ≤ n * (L + 3) := by
      calc
        _ ≤ ((List.finRange n).map fun _ => L + 3).sum := by
          apply List.sum_le_sum
          intro j _
          simpa only [Weights.materialize_get, coordinateCell_value] using conditional_bits sign (i = j) L input
        _ = _ := by simp
    omega

def replicateTrace (count : ℕ) (q : ℚ) : Traced (Vector ℚ count) :=
  Weights.materialize (fun _ : Fin count => emit .write [(Code.ofRat q).bits] q)
    (fun value : ℚ => (Code.ofRat value).bits)

@[simp] theorem replicateTrace_value (count : ℕ) (q : ℚ) :
    (replicateTrace count q).value = Vector.replicate count q := by
  apply Vector.ext
  intro i hi
  simp [replicateTrace, Weights.materialize]

theorem replicateTrace_count (count : ℕ) (q : ℚ) :
    (replicateTrace count q).events.length ≤ 3 * count + 1 := by
  have bound := Weights.materialize_count
    (fun _ : Fin count => emit .write [(Code.ofRat q).bits] q)
    (fun value : ℚ => (Code.ofRat value).bits) 1 (by intro i; exact le_rfl)
  simpa only [replicateTrace, Nat.reduceAdd, Nat.mul_comm] using bound

theorem replicateTrace_words (count : ℕ) (q : ℚ) :
    WordsWithin (count + (Code.ofRat q).bits) (replicateTrace count q).events := by
  apply Weights.materialize_words
  · omega
  · intro i
    simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq, and_true]
    omega
  · intro i
    simp only [emit_value]
    omega

def rowWidth (row : Vector ℚ n) : ℕ :=
  ((List.finRange n).map fun j => (Code.ofRat row[j.val]).bits).sum

def boxedTrace (input : Stored (n := n) (m := m)) : Traced (Stored (n := n) (m := m + (n + n))) := do
  let upper ← coordinateRowsTrace n 1
  let lower ← coordinateRowsTrace n (-1)
  let newRows ← appendVector upper lower rowWidth
  let ones ← replicateTrace n 1
  let zeros ← replicateTrace n 0
  let newBounds ← appendVector ones zeros (fun q : ℚ => (Code.ofRat q).bits)
  let coefficients ← appendVector input.coefficients newRows rowWidth
  let bounds ← appendVector input.bounds newBounds (fun q : ℚ => (Code.ofRat q).bits)
  let objective ← emit .read [n.size] input.objective
  emit .cons [m.size, n.size] ⟨coefficients, bounds, objective⟩

@[simp] theorem boxedTrace_value (input : Stored (n := n) (m := m)) :
    (boxedTrace input).value = input.boxed := by
  simp [boxedTrace, Stored.boxed, Stored.extend]

def slackTrace (input : Stored (n := n) (m := m)) (epsilon : ℚ) : Traced (Stored (n := n) (m := m)) := do
  let coefficients ← emit .read [m.size, n.size] input.coefficients
  let bounds ← Weights.materialize (fun i : Fin m => do
    let b ← readRat input.bounds i
    ratAdd b epsilon) (fun q : ℚ => (Code.ofRat q).bits)
  let objective ← emit .read [n.size] input.objective
  emit .cons [m.size, n.size] ⟨coefficients, bounds, objective⟩

@[simp] theorem slackTrace_value (input : Stored (n := n) (m := m)) (epsilon : ℚ) :
    (slackTrace input epsilon).value = input.slack epsilon := by
  change Stored.mk _ _ _ = Stored.mk _ _ _
  congr 1
  apply Vector.ext
  intro i hi
  simp [slackTrace, Stored.slack, Weights.materialize, readRat]

theorem boxedTrace_count (input : Stored (n := n) (m := m)) :
    (boxedTrace input).events.length ≤ 10 * n * n + 42 * n + 6 * m + 10 := by
  have upper := coordinateRowsTrace_count n 1
  have lower := coordinateRowsTrace_count n (-1)
  have ones := replicateTrace_count n 1
  have zeros := replicateTrace_count n 0
  simp only [boxedTrace, Traced.bind_events, Traced.bind_value, emit_value,
    List.length_append, appendVector_count, emit_length]
  nlinarith

theorem slackTrace_count (input : Stored (n := n) (m := m)) (epsilon : ℚ) :
    (slackTrace input epsilon).events.length ≤ 5 * m + 4 := by
  have cells := Weights.materialize_count (fun i : Fin m => do
    let b ← readRat input.bounds i
    ratAdd b epsilon) (fun q : ℚ => (Code.ofRat q).bits) 3 (by intro i; exact le_rfl)
  simp only [slackTrace, Traced.bind_events, Traced.bind_value, emit_value,
    List.length_append, emit_length]
  nlinarith

theorem slackTrace_words (input : Stored (n := n) (m := m)) (epsilon : ℚ) (L : ℕ)
    (bounds : ∀ i : Fin m, (Code.ofRat input.bounds[i.val]).bits ≤ L) :
    WordsWithin (m + n + 2 * (L + (Code.ofRat epsilon).bits) + 10) (slackTrace input epsilon).events := by
  let K := m + n + 2 * (L + (Code.ofRat epsilon).bits) + 10
  have cells : ∀ i : Fin m, WordsWithin K ((do
      let b ← readRat input.bounds i
      ratAdd b epsilon) : Traced ℚ).events := by
    intro i
    have index : i.val.size ≤ m := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt i.isLt)
    have arithmetic := WordsWithin.mono (ratAdd_words input.bounds[i.val] epsilon)
      (show 2 * ((Code.ofRat input.bounds[i.val]).bits + (Code.ofRat epsilon).bits) + 8 ≤ K by
        dsimp [K]; have := bounds i; omega)
    simp only [Traced.bind_events, Traced.bind_value, readRat, emit_value, wordsWithin_append]
    refine ⟨?_, arithmetic⟩
    simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, and_true]
    dsimp [K]
    have := bounds i
    constructor <;> omega
  have values : ∀ i : Fin m, (Code.ofRat ((do
      let b ← readRat input.bounds i
      ratAdd b epsilon) : Traced ℚ).value).bits ≤ K := by
    intro i
    have arithmetic := ratAdd_result_bits input.bounds[i.val] epsilon
    change (Code.ofRat (input.bounds[i.val] + epsilon)).bits ≤ K
    dsimp [K]
    have := bounds i
    omega
  have stored := Weights.materialize_words _ (fun q : ℚ => (Code.ofRat q).bits) K (by dsimp [K]; omega) cells values
  have nSize : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have mSize : m.size ≤ m := Nat.size_le.mpr Nat.lt_two_pow_self
  change WordsWithin K _
  simp only [slackTrace, Traced.bind_events, Traced.bind_value, emit_value, wordsWithin_append,
    emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, and_true]
  refine ⟨⟨?_, ?_⟩, stored, ?_, ?_, ?_⟩
  all_goals dsimp [K]; omega

end BuyAtBulk.PolynomialLP.InputTrace
