import BuyAtBulk.Computation.PolynomialLP.IntegerTrace
import BuyAtBulk.Computation.PolynomialLP.BudgetTrace

/-! Stored denominator clearing with a cached common denominator per row.
The returned table is exactly IntegerData.integerize. -/
namespace BuyAtBulk.PolynomialLP.InputTrace
open Computation.Runtime Computation.Rational
variable {n m : ℕ}

def IntegerRow.width (row : IntegerRow n) : ℕ :=
  ((List.finRange n).map fun j => row.coefficients[j.val].natAbs.size + 1).sum +
    row.bound.natAbs.size + 1

def integerRowsTrace (input : Stored (n := n) (m := m)) : Traced (Vector (IntegerRow n) m) :=
  Weights.materialize (fun i : Fin m => do
    let row ← emit .read [i.val.size, n.size] input.coefficients[i.val]
    let bound ← readRat input.bounds i
    integerRowTrace row bound) IntegerRow.width

@[simp] theorem integerRowsTrace_get (input : Stored (n := n) (m := m)) (i : Fin m) :
    (integerRowsTrace input).value[i.val] = integerRow input.coefficients[i.val] input.bounds[i.val] := by
  simp [integerRowsTrace, Weights.materialize, readRat]

def integerCast (z : ℤ) : Traced ℚ :=
  emit .ratCast [z.natAbs.size + 1, (Code.ofRat (z : ℚ)).bits] (z : ℚ)

@[simp] theorem integerCast_value (z : ℤ) : (integerCast z).value = (z : ℚ) := rfl
@[simp] theorem integerCast_count (z : ℤ) : (integerCast z).events.length = 1 := rfl

def castRow (row : Vector ℤ n) : Traced (Vector ℚ n) :=
  Weights.materialize (fun j : Fin n => do
    let z ← emit .read [j.val.size, row[j.val].natAbs.size + 1] row[j.val]
    integerCast z) (fun q : ℚ => (Code.ofRat q).bits)

@[simp] theorem castRow_get (row : Vector ℤ n) (j : Fin n) :
    (castRow row).value[j.val] = (row[j.val] : ℚ) := by simp [castRow, Weights.materialize]

def castMatrix (rows : Vector (IntegerRow n) m) : Traced (Vector (Vector ℚ n) m) :=
  Weights.materialize (fun i : Fin m => do
    let row ← emit .read [i.val.size, IntegerRow.width rows[i.val]] rows[i.val]
    castRow row.coefficients) (fun row : Vector ℚ n =>
      ((List.finRange n).map fun j => (Code.ofRat row[j.val]).bits).sum)

def castBounds (rows : Vector (IntegerRow n) m) : Traced (Vector ℚ m) :=
  Weights.materialize (fun i : Fin m => do
    let z ← emit .read [i.val.size, rows[i.val].bound.natAbs.size + 1] rows[i.val].bound
    integerCast z) (fun q : ℚ => (Code.ofRat q).bits)

def integerizeTrace (input : Stored (n := n) (m := m)) : Traced (Stored (n := n) (m := m)) := do
  let rows ← integerRowsTrace input
  let coefficients ← castMatrix rows
  let bounds ← castBounds rows
  let objective ← emit .read [n.size] input.objective
  emit .cons [m.size, n.size] ⟨coefficients, bounds, objective⟩

@[simp] theorem integerizeTrace_value (input : Stored (n := n) (m := m)) :
    (integerizeTrace input).value = integerize input := by
  change Stored.mk _ _ _ = Stored.mk _ _ _
  congr 1
  · apply Vector.ext
    intro i hi
    apply Vector.ext
    intro j hj
    simp [integerizeTrace, integerize, castMatrix, Weights.materialize, castRow, integerRowsTrace, readRat]
  · apply Vector.ext
    intro i hi
    simp [integerizeTrace, integerize, castBounds, Weights.materialize, integerRowsTrace, readRat]

theorem integerRowsTrace_count (input : Stored (n := n) (m := m)) :
    (integerRowsTrace input).events.length ≤ m * (17 * n + 14) + 1 := by
  apply Weights.materialize_count _ _ (17 * n + 12)
  intro i
  have row := integerRowTrace_count input.coefficients[i.val] input.bounds[i.val]
  simp only [Traced.bind_events, Traced.bind_value, emit_value, List.length_append,
    emit_length, readRat]
  omega

theorem castRow_count (row : Vector ℤ n) : (castRow row).events.length ≤ 4 * n + 1 := by
  have count := Weights.materialize_count
    (fun j : Fin n => do
      let z ← emit .read [j.val.size, row[j.val].natAbs.size + 1] row[j.val]
      integerCast z) (fun q : ℚ => (Code.ofRat q).bits) 2 (by intro j; exact le_rfl)
  simpa only [castRow, Nat.reduceAdd, Nat.mul_comm] using count

theorem castMatrix_count (rows : Vector (IntegerRow n) m) :
    (castMatrix rows).events.length ≤ m * (4 * n + 4) + 1 := by
  apply Weights.materialize_count _ _ (4 * n + 2)
  intro i
  have row := castRow_count rows[i.val].coefficients
  simp only [Traced.bind_events, Traced.bind_value, emit_value, List.length_append, emit_length]
  omega

theorem castBounds_count (rows : Vector (IntegerRow n) m) :
    (castBounds rows).events.length ≤ 4 * m + 1 := by
  have count := Weights.materialize_count
    (fun i : Fin m => do
      let z ← emit .read [i.val.size, rows[i.val].bound.natAbs.size + 1] rows[i.val].bound
      integerCast z) (fun q : ℚ => (Code.ofRat q).bits) 2 (by intro i; exact le_rfl)
  simpa only [castBounds, Nat.reduceAdd, Nat.mul_comm] using count

theorem integerizeTrace_count (input : Stored (n := n) (m := m)) :
    (integerizeTrace input).events.length ≤ m * (21 * n + 22) + 5 := by
  have rows := integerRowsTrace_count input
  have matrix := castMatrix_count (integerRowsTrace input).value
  have bounds := castBounds_count (integerRowsTrace input).value
  simp only [integerizeTrace, Traced.bind_events, Traced.bind_value, emit_value,
    List.length_append, emit_length]
  nlinarith

end BuyAtBulk.PolynomialLP.InputTrace
