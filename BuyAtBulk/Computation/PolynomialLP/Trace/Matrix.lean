import BuyAtBulk.Computation.PolynomialLP.EllipsoidData
import BuyAtBulk.Computation.Runtime.Weights

/-! Actual stored matrix arithmetic. Materialized index lists are charged and
reused by row scans; every rational multiply/add is the closed traced primitive. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace BuyAtBulk.PolynomialLP.Trace
open BuyAtBulk.Computation BuyAtBulk.Computation.Runtime
open Rational
variable {n : ℕ}

def matrixRow (shape : Vector (Vector ℚ n) n) (direction : Vector ℚ n)
    (indices : List (Fin n)) (i : Fin n) : Traced ℚ := do
  let row ← emit .read [i.val.size, n.size] shape[i.val]
  dotScan row direction indices

@[simp] theorem matrixRow_value (shape : Vector (Vector ℚ n) n) (direction : Vector ℚ n)
    (indices : List (Fin n)) (i : Fin n) :
    (matrixRow shape direction indices i).value =
      (indices.map fun j => shape[i.val][j.val] * direction[j.val]).sum := by
  simp only [matrixRow, Traced.bind_value, emit_value, dotScan_value]

@[simp] theorem matrixRow_count (shape : Vector (Vector ℚ n) n) (direction : Vector ℚ n)
    (indices : List (Fin n)) (i : Fin n) :
    (matrixRow shape direction indices i).events.length = 7 * indices.length + 1 := by
  simp only [matrixRow, Traced.bind_events, Traced.bind_value, emit_value, emit_length,
    List.length_append, dotScan_count]
  omega

def matrixVector (shape : Vector (Vector ℚ n) n) (direction : Vector ℚ n) : Traced (Vector ℚ n) :=
  let indices := indexList n
  let values := Weights.materialize (matrixRow shape direction indices.value) (fun q => (Code.ofRat q).bits)
  ⟨values.value, indices.events ++ values.events⟩

@[simp] theorem matrixVector_get (shape : Vector (Vector ℚ n) n) (direction : Vector ℚ n) (i : Fin n) :
    (matrixVector shape direction).value[i.val] =
      ((List.finRange n).map fun j => shape[i.val][j.val] * direction[j.val]).sum := by
  simp only [matrixVector, Weights.materialize_get, matrixRow_value, indexList_value]

theorem matrixVector_value (shape : Vector (Vector ℚ n) n) (direction : Vector ℚ n) :
    (matrixVector shape direction).value = PolynomialLP.matrixVector shape direction := by
  apply Vector.ext
  intro i bound
  simpa only [PolynomialLP.matrixVector, Vector.getElem_ofFn] using matrixVector_get shape direction ⟨i, bound⟩

theorem matrixVector_count (shape : Vector (Vector ℚ n) n) (direction : Vector ℚ n) :
    (matrixVector shape direction).events.length ≤ 7 * n ^ 2 + 6 * n + 1 := by
  have values := Weights.materialize_count (matrixRow shape direction (List.finRange n))
    (fun q => (Code.ofRat q).bits) (7 * n + 1) (by intro i; simp)
  simp only [matrixVector, List.length_append, indexList_value, indexList_count]
  nlinarith

def quadratic (shape : Vector (Vector ℚ n) n) (direction : Vector ℚ n) : Traced ℚ :=
  let image := matrixVector shape direction
  let indices := indexList n
  let result := dotScan direction image.value indices.value
  ⟨result.value, image.events ++ indices.events ++ result.events⟩

theorem quadratic_value (shape : Vector (Vector ℚ n) n) (direction : Vector ℚ n) :
    (quadratic shape direction).value = PolynomialLP.quadratic shape direction := by
  simp only [quadratic, dotScan_value, matrixVector_value, indexList_value, PolynomialLP.quadratic]

theorem quadratic_count (shape : Vector (Vector ℚ n) n) (direction : Vector ℚ n) :
    (quadratic shape direction).events.length ≤ 7 * n ^ 2 + 16 * n + 1 := by
  have image := matrixVector_count shape direction
  simp only [quadratic, List.length_append, indexList_count, dotScan_count, indexList_value, List.length_finRange]
  omega

end BuyAtBulk.PolynomialLP.Trace
