import BuyAtBulk.Computation.PolynomialLP.DenominatorTrace

/-! Closed integer division/multiplication used to clear one rational scalar.
All events carry the signed input and result widths; no runtime field is
accepted from the caller. -/
namespace BuyAtBulk.PolynomialLP.InputTrace
open Computation.Runtime Computation.Rational
variable {n : ℕ}

def clearScalarTrace (q : ℚ) (D : ℕ) : Traced ℤ := do
  let numerator ← emit .read [q.num.natAbs.size + 1] q.num
  let denominator ← emit .read [q.den.size + 1] q.den
  let common ← emit .read [D.size + 1] D
  let quotient ← emit .intDiv [common.size + 1, denominator.size + 1,
    (common / denominator).size + 1] (common / denominator)
  emit .intMul [numerator.natAbs.size + 1, quotient.size + 1,
    (numerator * (quotient : ℤ)).natAbs.size + 1] (numerator * (quotient : ℤ))

@[simp] theorem clearScalarTrace_value (q : ℚ) (D : ℕ) :
    (clearScalarTrace q D).value = clearScalar q D := rfl
@[simp] theorem clearScalarTrace_count (q : ℚ) (D : ℕ) :
    (clearScalarTrace q D).events.length = 5 := rfl

theorem clearScalarTrace_words (q : ℚ) (D L P : ℕ)
    (input : (Code.ofRat q).Bounded L) (denominator : D ≤ 2 ^ P) :
    WordsWithin (L + P + 3) (clearScalarTrace q D).events := by
  have numeratorSize : q.num.natAbs.size ≤ L := Nat.size_le.mpr input.1
  have denominatorSize : q.den.size ≤ L := Nat.size_le.mpr (by
    simpa only [Code.ofRat, Int.natAbs_natCast] using input.2)
  have commonSize := Nat.size_le_size denominator
  rw [Nat.size_pow] at commonSize
  have quotientSize : (D / q.den).size ≤ D.size := Nat.size_le_size (Nat.div_le_self _ _)
  have product : (q.num * (D / q.den : ℕ)).natAbs ≤ 2 ^ (L + P) := by
    simp only [Int.natAbs_mul, Int.natAbs_natCast, pow_add]
    exact (Nat.mul_le_mul_left _ (Nat.div_le_self D q.den)).trans
      (Nat.mul_le_mul input.1.le denominator)
  have productSize := Nat.size_le_size product
  rw [Nat.size_pow] at productSize
  simp only [clearScalarTrace, Traced.bind_events, Traced.bind_value, emit_value, emit,
    wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
  repeat' apply And.intro
  all_goals omega

def integerRowTrace (row : Vector ℚ n) (bound : ℚ) : Traced (IntegerRow n) := do
  let D ← rowDenominatorTrace row bound
  let coefficients ← Computation.Runtime.Weights.materialize
    (fun j : Fin n => do
      let q ← readRat row j
      clearScalarTrace q D) (fun z : ℤ => z.natAbs.size + 1)
  let rhs ← clearScalarTrace bound D
  emit .cons [n.size] ⟨coefficients, rhs⟩

@[simp] theorem integerRowTrace_value (row : Vector ℚ n) (bound : ℚ) :
    (integerRowTrace row bound).value = integerRow row bound := by
  change IntegerRow.mk _ _ = IntegerRow.mk _ _
  congr 1
  · apply Vector.ext
    intro i hi
    simp [integerRowTrace, integerRow, Weights.materialize, readRat]
  · simp only [clearScalarTrace_value, rowDenominatorTrace_value]

theorem integerRowTrace_count (row : Vector ℚ n) (bound : ℚ) :
    (integerRowTrace row bound).events.length ≤ 17 * n + 10 := by
  have cells := Computation.Runtime.Weights.materialize_count
    (fun j : Fin n => do
      let q ← readRat row j
      clearScalarTrace q (rowDenominator row bound))
    (fun z : ℤ => z.natAbs.size + 1) 6 (by intro j; exact le_rfl)
  simp only [integerRowTrace, Traced.bind_events, Traced.bind_value, List.length_append,
    rowDenominatorTrace_value, rowDenominatorTrace_count, clearScalarTrace_count,
    emit_length]
  omega

theorem integerRowTrace_words (row : Vector ℚ n) (bound : ℚ) (L : ℕ)
    (inputs : ∀ j : Fin n, (Code.ofRat row[j.val]).Bounded L)
    (rhs : (Code.ofRat bound).Bounded L) :
    WordsWithin (16 * (n + 2) * (L + 2)) (integerRowTrace row bound).events := by
  let K := 16 * (n + 2) * (L + 2)
  have denBound := rowDenominator_bound row bound L inputs rhs
  have denWords := (rowDenominatorTrace_words row bound L inputs rhs).mono
    (show 4 * (n + 2) * (L + 2) ≤ K by dsimp [K]; nlinarith)
  have rowBounds := integerRow_bounds row bound L inputs rhs
  have cells : ∀ j : Fin n, WordsWithin K ((do
      let q ← readRat row j
      clearScalarTrace q (rowDenominator row bound)) : Traced ℤ).events := by
    intro j
    have qBits := Code.bounded_bits (inputs j)
    have index : j.val.size ≤ n := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt j.isLt)
    have scalar := (clearScalarTrace_words row[j.val] _ L _ (inputs j) denBound).mono
      (show L + (n + 1) * L + 3 ≤ K by dsimp [K]; nlinarith)
    simp only [Traced.bind_events, Traced.bind_value, readRat, emit_value, wordsWithin_append]
    refine ⟨?_, scalar⟩
    simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, and_true]
    dsimp [K]
    constructor <;> nlinarith
  have values : ∀ j : Fin n, ((do
      let q ← readRat row j
      clearScalarTrace q (rowDenominator row bound)) : Traced ℤ).value.natAbs.size + 1 ≤ K := by
    intro j
    have size := Nat.size_le.mpr (rowBounds.1 j)
    change (clearScalar row[j.val] (rowDenominator row bound)).natAbs.size + 1 ≤ _
    simp only [integerRow, Vector.getElem_map] at size
    dsimp [K]
    nlinarith
  have stored := Weights.materialize_words _ (fun z : ℤ => z.natAbs.size + 1) K
    (by dsimp [K]; nlinarith) cells values
  have boundWords := (clearScalarTrace_words bound _ L _ rhs denBound).mono
    (show L + (n + 1) * L + 3 ≤ K by dsimp [K]; nlinarith)
  have dimension : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  change WordsWithin K _
  simp only [integerRowTrace, Traced.bind_events, Traced.bind_value, rowDenominatorTrace_value,
    wordsWithin_append, emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq, and_true]
  exact ⟨denWords, stored, boundWords, by dsimp [K]; nlinarith⟩

end BuyAtBulk.PolynomialLP.InputTrace
