import BuyAtBulk.Computation.PolynomialLP.IntegerizationTrace

/-! Binary widths of every stored integerized row and its casts. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP.InputTrace
open Computation.Runtime Computation.Rational
variable {n m : ℕ}

theorem integerCast_bits (z : ℤ) : (Code.ofRat (z : ℚ)).bits = z.natAbs.size + 3 := by
  simp [Code.bits, Code.ofRat]

theorem integerCast_words (z : ℤ) (P : ℕ) (bound : z.natAbs.size ≤ P) :
    WordsWithin (P + 3) (integerCast z).events := by
  simp only [integerCast, emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true, integerCast_bits]
  constructor <;> nlinarith

theorem integerRow_width_bound (row : IntegerRow n) (P : ℕ)
    (coefficients : ∀ j : Fin n, row.coefficients[j.val].natAbs.size ≤ P)
    (bound : row.bound.natAbs.size ≤ P) : IntegerRow.width row ≤ (n + 1) * (P + 1) := by
  have sum : ((List.finRange n).map fun j => row.coefficients[j.val].natAbs.size + 1).sum ≤ n * (P + 1) := by
    calc
      _ ≤ ((List.finRange n).map fun _ => P + 1).sum :=
        List.sum_le_sum (fun j _ => Nat.add_le_add_right (coefficients j) 1)
      _ = _ := by simp
  unfold IntegerRow.width
  nlinarith

theorem castRow_words (row : Vector ℤ n) (P : ℕ)
    (inputs : ∀ j : Fin n, row[j.val].natAbs.size ≤ P) :
    WordsWithin (4 * (n + 1) * (P + 4)) (castRow row).events := by
  apply Weights.materialize_words
  · nlinarith
  · intro j
    have index : j.val.size ≤ n := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt j.isLt)
    have cast := (integerCast_words row[j.val] P (inputs j)).mono
      (show P + 3 ≤ 4 * (n + 1) * (P + 4) by nlinarith)
    simp only [Traced.bind_events, Traced.bind_value, emit_value, wordsWithin_append]
    refine ⟨?_, cast⟩
    simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, and_true]
    constructor <;> nlinarith [inputs j]
  · intro j
    simp only [Traced.bind_value, emit_value, integerCast_value, integerCast_bits]
    nlinarith [inputs j]

theorem castRow_width_bound (row : Vector ℤ n) (P : ℕ)
    (inputs : ∀ j : Fin n, row[j.val].natAbs.size ≤ P) :
    ((List.finRange n).map fun j => (Code.ofRat (castRow row).value[j.val]).bits).sum ≤ n * (P + 3) := by
  calc
    _ ≤ ((List.finRange n).map fun _ => P + 3).sum := by
      apply List.sum_le_sum
      intro j _
      rw [castRow_get, integerCast_bits]
      exact Nat.add_le_add_right (inputs j) 3
    _ = _ := by simp

theorem castMatrix_words (rows : Vector (IntegerRow n) m) (P : ℕ)
    (coefficients : ∀ i : Fin m, ∀ j : Fin n, rows[i.val].coefficients[j.val].natAbs.size ≤ P)
    (bounds : ∀ i : Fin m, rows[i.val].bound.natAbs.size ≤ P) :
    WordsWithin (m + n + (n + 1) * (P + 1) + 4 * (n + 1) * (P + 4) + n * (P + 3) + 10) (castMatrix rows).events := by
  let K := m + n + (n + 1) * (P + 1) + 4 * (n + 1) * (P + 4) + n * (P + 3) + 10
  apply Weights.materialize_words
  · omega
  · intro i
    have index : i.val.size ≤ m := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt i.isLt)
    have width := integerRow_width_bound rows[i.val] P (coefficients i) (bounds i)
    have row := (castRow_words rows[i.val].coefficients P (coefficients i)).mono
      (show 4 * (n + 1) * (P + 4) ≤ K by try dsimp [K]; omega)
    simp only [Traced.bind_events, Traced.bind_value, emit_value, wordsWithin_append]
    refine ⟨?_, row⟩
    simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, and_true]
    try dsimp [K]
    constructor <;> omega
  · intro i
    simp only [Traced.bind_value, emit_value]
    have width := castRow_width_bound rows[i.val].coefficients P (coefficients i)
    try dsimp [K]
    omega

theorem castBounds_words (rows : Vector (IntegerRow n) m) (P : ℕ)
    (bounds : ∀ i : Fin m, rows[i.val].bound.natAbs.size ≤ P) :
    WordsWithin (4 * (m + 1) * (P + 4)) (castBounds rows).events := by
  apply Weights.materialize_words
  · nlinarith
  · intro i
    have index : i.val.size ≤ m := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt i.isLt)
    have cast := (integerCast_words rows[i.val].bound P (bounds i)).mono
      (show P + 3 ≤ 4 * (m + 1) * (P + 4) by nlinarith)
    simp only [Traced.bind_events, Traced.bind_value, emit_value, wordsWithin_append]
    refine ⟨?_, cast⟩
    simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, and_true]
    constructor <;> nlinarith [bounds i]
  · intro i
    simp only [Traced.bind_value, emit_value, integerCast_value, integerCast_bits]
    nlinarith [bounds i]

theorem integerRowsTrace_words (input : Stored (n := n) (m := m)) (L : ℕ)
    (coefficients : ∀ i : Fin m, ∀ j : Fin n, (Code.ofRat input.coefficients[i.val][j.val]).Bounded L)
    (bounds : ∀ i : Fin m, (Code.ofRat input.bounds[i.val]).Bounded L) :
    WordsWithin (m + n + 2 * L + 2 + 16 * (n + 2) * (L + 2) + (n + 1) * ((n + 2) * L + 1) + 10) (integerRowsTrace input).events := by
  let K := m + n + 2 * L + 2 + 16 * (n + 2) * (L + 2) + (n + 1) * ((n + 2) * L + 1) + 10
  apply Weights.materialize_words
  · omega
  · intro i
    have index : i.val.size ≤ m := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt i.isLt)
    have dimension : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
    have boundBits := Code.bounded_bits (bounds i)
    have row := (integerRowTrace_words input.coefficients[i.val] input.bounds[i.val] L (coefficients i) (bounds i)).mono
      (show 16 * (n + 2) * (L + 2) ≤ K by try dsimp [K]; omega)
    simp only [Traced.bind_events, Traced.bind_value, emit_value, readRat, wordsWithin_append]
    refine ⟨?_, ?_, row⟩
    all_goals
      simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, forall_eq, and_true]
      try dsimp [K]
      constructor <;> omega
  · intro i
    simp only [Traced.bind_value, emit_value, readRat, integerRowTrace_value]
    have rowBounds := integerRow_bounds input.coefficients[i.val] input.bounds[i.val] L (coefficients i) (bounds i)
    have width := integerRow_width_bound (integerRow input.coefficients[i.val] input.bounds[i.val]) ((n + 2) * L)
      (fun j => Nat.size_le.mpr (rowBounds.1 j)) (Nat.size_le.mpr rowBounds.2)
    try dsimp [K]
    omega

def integerizeWordBudget (n m L : ℕ) : ℕ :=
  let P := (n + 2) * L
  (m + n + 2 * L + 2 + 16 * (n + 2) * (L + 2) + (n + 1) * (P + 1) + 10) +
    (m + n + (n + 1) * (P + 1) + 4 * (n + 1) * (P + 4) + n * (P + 3) + 10) +
    4 * (m + 1) * (P + 4) + m + n + 10

theorem integerizeTrace_words (input : Stored (n := n) (m := m)) (L : ℕ)
    (coefficients : ∀ i : Fin m, ∀ j : Fin n, (Code.ofRat input.coefficients[i.val][j.val]).Bounded L)
    (bounds : ∀ i : Fin m, (Code.ofRat input.bounds[i.val]).Bounded L) :
    WordsWithin (integerizeWordBudget n m L) (integerizeTrace input).events := by
  have rows := (integerRowsTrace_words input L coefficients bounds).mono
    (show _ ≤ integerizeWordBudget n m L by dsimp only [integerizeWordBudget]; omega)
  have cb : ∀ i : Fin m, ∀ j : Fin n,
      (integerRowsTrace input).value[i.val].coefficients[j.val].natAbs.size ≤ (n + 2) * L := by
    intro i j
    rw [integerRowsTrace_get]
    exact Nat.size_le.mpr ((integerRow_bounds _ _ L (coefficients i) (bounds i)).1 j)
  have bb : ∀ i : Fin m, (integerRowsTrace input).value[i.val].bound.natAbs.size ≤ (n + 2) * L := by
    intro i
    rw [integerRowsTrace_get]
    exact Nat.size_le.mpr (integerRow_bounds _ _ L (coefficients i) (bounds i)).2
  have matrix := (castMatrix_words (integerRowsTrace input).value _ cb bb).mono
    (show _ ≤ integerizeWordBudget n m L by dsimp only [integerizeWordBudget]; omega)
  have boundWords := (castBounds_words (integerRowsTrace input).value _ bb).mono
    (show _ ≤ integerizeWordBudget n m L by dsimp only [integerizeWordBudget]; omega)
  have nSize : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have mSize : m.size ≤ m := Nat.size_le.mpr Nat.lt_two_pow_self
  simp only [integerizeTrace, Traced.bind_events, Traced.bind_value, emit_value,
    wordsWithin_append, emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
  refine ⟨rows, matrix, boundWords, ?_, ?_, ?_⟩
  all_goals dsimp only [integerizeWordBudget]; omega

/-- The full preprocessing runtime is derived from actual stored input. -/
theorem integerizeTrace_runtime (input : Stored (n := n) (m := m)) :
    (integerizeTrace input).value = integerize input ∧
    (integerizeTrace input).events.length ≤ m * (21 * n + 22) + 5 ∧
    WordsWithin (integerizeWordBudget n m (inputBudget input)) (integerizeTrace input).events :=
  ⟨integerizeTrace_value input, integerizeTrace_count input,
    integerizeTrace_words input _ (inputBudget_coefficient input) (inputBudget_bound input)⟩

end BuyAtBulk.PolynomialLP.InputTrace
