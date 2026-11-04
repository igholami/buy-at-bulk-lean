import BuyAtBulk.Computation.PolynomialLP.InputTrace

/-! The common row denominator is computed once from its stored scalar
entries. Every actual product prefix has a linear binary exponent bound. -/
namespace BuyAtBulk.PolynomialLP.InputTrace
open Computation.Runtime Computation.Rational
variable {n : ℕ}

def denominatorScan (row : Vector ℚ n) : List (Fin n) → Traced ℕ
  | [] => emit .write [1] 1
  | j :: rest => do
      let _ ← emit .scan [j.val.size] ()
      let q ← readRat row j
      let d ← emit .read [q.den.size] q.den
      let _ ← emit .recurse [rest.length.size] ()
      let tail ← denominatorScan row rest
      let product ← emit .natMul [d.size, tail.size, (d * tail).size] (d * tail)
      emit .write [product.size] product

@[simp] theorem denominatorScan_value (row : Vector ℚ n) (indices : List (Fin n)) :
    (denominatorScan row indices).value = (indices.map fun j => row[j.val].den).prod := by
  induction indices with
  | nil => rfl
  | cons j rest ih => simp [denominatorScan, readRat, emit, ih]

theorem denominatorScan_count (row : Vector ℚ n) (indices : List (Fin n)) :
    (denominatorScan row indices).events.length = 6 * indices.length + 1 := by
  induction indices with
  | nil => rfl
  | cons j rest ih =>
    simp only [denominatorScan, Traced.bind_events, Traced.bind_value, emit_value,
      List.length_append, emit_length, readRat, List.length_cons, ih]
    omega

theorem denominator_product_bound (row : Vector ℚ n) (indices : List (Fin n)) (L : ℕ)
    (inputs : ∀ j ∈ indices, (Code.ofRat row[j.val]).Bounded L) :
    (indices.map fun j => row[j.val].den).prod ≤ 2 ^ (indices.length * L) := by
  induction indices with
  | nil => simp
  | cons j rest ih =>
    have bound : row[j.val].den ≤ 2 ^ L := by
      simpa only [Code.ofRat, Int.natAbs_natCast] using (inputs j (by simp)).2.le
    have tail := ih (fun k member => inputs k (by simp [member]))
    calc
      _ ≤ 2 ^ L * 2 ^ (rest.length * L) := Nat.mul_le_mul bound tail
      _ = _ := by rw [← pow_add]; congr 1; simp only [List.length_cons]; ring

theorem denominatorScan_words (row : Vector ℚ n) (indices : List (Fin n)) (L : ℕ)
    (inputs : ∀ j ∈ indices, (Code.ofRat row[j.val]).Bounded L) :
    WordsWithin (2 * (n + indices.length + 1) * (L + 2)) (denominatorScan row indices).events := by
  induction indices with
  | nil => simp [denominatorScan, emit, WordsWithin]; nlinarith
  | cons j rest ih =>
    have current := inputs j (by simp)
    have tailInputs : ∀ k ∈ rest, (Code.ofRat row[k.val]).Bounded L :=
      fun k member => inputs k (by simp [member])
    have tail := ih tailInputs
    have tailBound := denominator_product_bound row rest L tailInputs
    have totalBound := denominator_product_bound row (j :: rest) L inputs
    have tailSize := Nat.size_le_size tailBound
    have totalSize := Nat.size_le_size totalBound
    simp only [Nat.size_pow] at tailSize totalSize
    have qb := Code.bounded_bits current
    have db : row[j.val].den.size ≤ L := Nat.size_le.mpr (by
      simpa only [Code.ofRat, Int.natAbs_natCast] using current.2)
    have ji : j.val.size ≤ n := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt j.isLt)
    have ri : rest.length.size ≤ rest.length := Nat.size_le.mpr Nat.lt_two_pow_self
    have totalSize' : (row[j.val].den * (rest.map fun k => row[k.val].den).prod).size ≤
        (rest.length + 1) * L + 1 := by simpa using totalSize
    simp only [denominatorScan, Traced.bind_events, Traced.bind_value, emit_value,
      readRat, denominatorScan_value, wordsWithin_append, emit, wordsWithin_cons,
      wordsWithin_nil, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, and_true, List.length_cons]
    repeat' apply And.intro
    all_goals first
      | exact tail.mono (by nlinarith)
      | nlinarith

def rowDenominatorTrace (row : Vector ℚ n) (bound : ℚ) : Traced ℕ := do
  let indices ← indexList n
  let d ← emit .read [bound.den.size] bound.den
  let product ← denominatorScan row indices
  emit .natMul [d.size, product.size, (d * product).size] (d * product)

@[simp] theorem rowDenominatorTrace_value (row : Vector ℚ n) (bound : ℚ) :
    (rowDenominatorTrace row bound).value = rowDenominator row bound := by
  simp [rowDenominatorTrace, rowDenominator, Fin.prod_univ_def]

theorem rowDenominatorTrace_count (row : Vector ℚ n) (bound : ℚ) :
    (rowDenominatorTrace row bound).events.length = 9 * n + 3 := by
  simp only [rowDenominatorTrace, Traced.bind_events, Traced.bind_value, emit_value,
    List.length_append, emit_length, indexList_count, indexList_value, denominatorScan_count,
    List.length_finRange]
  omega

theorem rowDenominatorTrace_words (row : Vector ℚ n) (bound : ℚ) (L : ℕ)
    (inputs : ∀ j : Fin n, (Code.ofRat row[j.val]).Bounded L)
    (rhs : (Code.ofRat bound).Bounded L) :
    WordsWithin (4 * (n + 2) * (L + 2)) (rowDenominatorTrace row bound).events := by
  have scan := denominatorScan_words row (List.finRange n) L (fun j _ => inputs j)
  have product := denominator_product_bound row (List.finRange n) L (fun j _ => inputs j)
  have total := rowDenominator_bound row bound L inputs rhs
  have productSize := Nat.size_le_size product
  have totalSize := Nat.size_le_size total
  simp only [List.length_finRange, Nat.size_pow] at scan product productSize totalSize
  have db : bound.den.size ≤ L := Nat.size_le.mpr (by
    simpa only [Code.ofRat, Int.natAbs_natCast] using rhs.2)
  have initial := indexList_words n (4 * (n + 2) * (L + 2)) (by nlinarith)
  simp only [rowDenominatorTrace, Traced.bind_events, Traced.bind_value, emit_value,
    indexList_value, denominatorScan_value, wordsWithin_append, emit, wordsWithin_cons,
    wordsWithin_nil, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, and_true]
  refine ⟨initial, ?_, scan.mono (by nlinarith), ?_⟩
  · nlinarith
  · have totalSize' : (bound.den * ((List.finRange n).map fun j => row[j.val].den).prod).size ≤
        (n + 1) * L + 1 := by
      simpa only [rowDenominator, Fin.prod_univ_def] using totalSize
    repeat' apply And.intro
    all_goals nlinarith

end BuyAtBulk.PolynomialLP.InputTrace
