import BuyAtBulk.Computation.PolynomialLP.Trace.Matrix
import BuyAtBulk.Computation.PolynomialLP.Trace.Schedule

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace BuyAtBulk.PolynomialLP.Trace
open BuyAtBulk.Computation BuyAtBulk.Computation.Runtime
open Rational
variable {n : ℕ}

@[simp] theorem materialize_getNat {α : Type} (f : Fin n → Traced α) (width : α → ℕ)
    (i : ℕ) (bound : i < n) : (Weights.materialize f width).value[i] = (f ⟨i,bound⟩).value :=
  Weights.materialize_get f width ⟨i,bound⟩

def negate (q : ℚ) : Traced ℚ :=
  emit .ratNeg [(Code.ofRat q).bits, (Code.ofRat (-q)).bits] (-q)
def subtract (a b : ℚ) : Traced ℚ := do
  let negative ← negate b
  ratAdd a negative
@[simp] theorem negate_value (q : ℚ) : (negate q).value = -q := rfl
@[simp] theorem negate_count (q : ℚ) : (negate q).events.length = 1 := rfl
@[simp] theorem subtract_value (a b : ℚ) : (subtract a b).value = a-b := by
  simp [subtract, sub_eq_add_neg]
@[simp] theorem subtract_count (a b : ℚ) : (subtract a b).events.length = 3 := by
  simp [subtract, Traced.bind_events, List.length_append]

def centerCell (center image : Vector ℚ n) (denominator : ℚ) (i : Fin n) : Traced ℚ := do
  let c ← readRat center i
  let u ← readRat image i
  let quotient ← ratDiv u denominator
  subtract c quotient
@[simp] theorem centerCell_value (center image : Vector ℚ n) (denominator : ℚ) (i : Fin n) :
    (centerCell center image denominator i).value = center[i.val]-image[i.val]/denominator := by
  simp [centerCell, readRat]
@[simp] theorem centerCell_count (center image : Vector ℚ n) (denominator : ℚ) (i : Fin n) :
    (centerCell center image denominator i).events.length = 7 := by
  simp [centerCell, Traced.bind_events, List.length_append, readRat, emit]

def rawCenter (state : Ellipsoid n) (direction : Vector ℚ n) : Traced (Vector ℚ n) :=
  let image := matrixVector state.shape direction
  let q := quadratic state.shape direction
  let root := normalizationRoot q.value n
  let dimension := ratCast n
  let successor := ratAdd dimension.value 1
  let denominator := ratMul successor.value root.value
  let output := Weights.materialize (centerCell state.center image.value denominator.value)
    (fun q => (Code.ofRat q).bits)
  ⟨output.value, image.events ++ q.events ++ root.events ++ dimension.events ++
    successor.events ++ denominator.events ++ output.events⟩

theorem rawCenter_value (state : Ellipsoid n) (direction : Vector ℚ n) :
    (rawCenter state direction).value = state.rawCenter direction := by
  simp only [rawCenter, Traced.bind_value, matrixVector_value, quadratic_value,
    normalizationRoot_value, ratCast, emit_value, ratAdd_value, ratMul_value]
  apply Vector.ext
  intro i bound
  simp only [materialize_getNat, centerCell_value, Ellipsoid.rawCenter, Vector.getElem_ofFn]

theorem rawCenter_count (state : Ellipsoid n) (direction : Vector ℚ n) :
    (rawCenter state direction).events.length ≤
      14*n^2+31*n+8+40*((Code.ofRat (PolynomialLP.quadratic state.shape direction)).bits+256*n*(n+1)+3) := by
  have a := matrixVector_count state.shape direction
  have b := quadratic_count state.shape direction
  have c := normalizationRoot_count (PolynomialLP.quadratic state.shape direction) n
  have d := Weights.materialize_count (centerCell state.center
    (PolynomialLP.matrixVector state.shape direction)
    (((n:ℚ)+1)*PolynomialLP.normalizationRoot (PolynomialLP.quadratic state.shape direction) n))
    (fun q => (Code.ofRat q).bits) 7 (by intro i; simp)
  simp only [rawCenter, Traced.bind_events, Traced.bind_value, List.length_append,
    matrixVector_value, quadratic_value, normalizationRoot_value, ratCast, emit_length,
    emit_value, ratAdd_length, ratAdd_value, ratMul_length, ratMul_value]
  omega

def shapeCell (shape : Vector (Vector ℚ n) n) (image : Vector ℚ n) (alpha beta : ℚ)
    (i j : Fin n) : Traced ℚ := do
  let row ← emit .read [i.val.size, n.size] shape[i.val]
  let z ← readRat row j
  let u ← readRat image i
  let v ← readRat image j
  let first ← ratMul beta u
  let second ← ratMul first v
  let residual ← subtract z second
  ratMul alpha residual
@[simp] theorem shapeCell_value (shape : Vector (Vector ℚ n) n) (image : Vector ℚ n)
    (alpha beta : ℚ) (i j : Fin n) :
    (shapeCell shape image alpha beta i j).value = alpha*(shape[i.val][j.val]-beta*image[i.val]*image[j.val]) := by
  simp [shapeCell, readRat]
@[simp] theorem shapeCell_count (shape : Vector (Vector ℚ n) n) (image : Vector ℚ n)
    (alpha beta : ℚ) (i j : Fin n) :
    (shapeCell shape image alpha beta i j).events.length = 13 := by
  simp [shapeCell, Traced.bind_events, List.length_append, readRat, emit]

def shapeRows (shape : Vector (Vector ℚ n) n) (image : Vector ℚ n) (alpha beta : ℚ) :
    Traced (Vector (Vector ℚ n) n) :=
  Weights.materialize (fun i => Weights.materialize (shapeCell shape image alpha beta i)
    (fun q => (Code.ofRat q).bits)) (fun _ => n.size)

theorem shapeRows_count (shape : Vector (Vector ℚ n) n) (image : Vector ℚ n) (alpha beta : ℚ) :
    (shapeRows shape image alpha beta).events.length ≤ 15*n^2+3*n+1 := by
  have row (i : Fin n) := Weights.materialize_count (shapeCell shape image alpha beta i)
    (fun q => (Code.ofRat q).bits) 13 (by intro j; simp)
  have all := Weights.materialize_count (fun i => Weights.materialize (shapeCell shape image alpha beta i)
    (fun q => (Code.ofRat q).bits)) (fun _ => n.size) (15*n+1) (by intro i; simpa [Nat.mul_comm] using row i)
  dsimp only [shapeRows]
  nlinarith

def rawShape (state : Ellipsoid n) (direction : Vector ℚ n) : Traced (Vector (Vector ℚ n) n) :=
  let image := matrixVector state.shape direction
  let q := quadratic state.shape direction
  let dimension := ratCast n
  let square := ratMul dimension.value dimension.value
  let predecessor := subtract square.value 1
  let alpha := ratDiv square.value predecessor.value
  let successor := ratAdd dimension.value 1
  let denominator := ratMul successor.value q.value
  let beta := ratDiv 2 denominator.value
  let output := shapeRows state.shape image.value alpha.value beta.value
  ⟨output.value, image.events ++ q.events ++ dimension.events ++ square.events ++
    predecessor.events ++ alpha.events ++ successor.events ++ denominator.events ++
    beta.events ++ output.events⟩

theorem rawShape_value (state : Ellipsoid n) (direction : Vector ℚ n) :
    (rawShape state direction).value = state.rawShape direction := by
  simp only [rawShape, Traced.bind_value, matrixVector_value, quadratic_value,
    ratCast, emit_value, ratAdd_value, ratMul_value, ratDiv_value, subtract_value]
  apply Vector.ext
  intro i bound
  apply Vector.ext
  intro j boundj
  simp only [shapeRows, materialize_getNat, shapeCell_value, Ellipsoid.rawShape,
    Vector.getElem_ofFn, pow_two]

theorem rawShape_count (state : Ellipsoid n) (direction : Vector ℚ n) :
    (rawShape state direction).events.length ≤ 29*n^2+25*n+18 := by
  have a := matrixVector_count state.shape direction
  have b := quadratic_count state.shape direction
  have c := shapeRows_count state.shape (PolynomialLP.matrixVector state.shape direction)
    ((n:ℚ)^2/((n:ℚ)^2-1)) (2/(((n:ℚ)+1)*PolynomialLP.quadratic state.shape direction))
  simp only [rawShape, Traced.bind_events, Traced.bind_value, List.length_append,
    matrixVector_value, quadratic_value, ratCast, emit_length, emit_value,
    ratAdd_length, ratAdd_value, ratMul_length, ratMul_value, ratDiv_length, ratDiv_value,
    subtract_count, subtract_value]
  simp only [pow_two] at c
  nlinarith

end BuyAtBulk.PolynomialLP.Trace
