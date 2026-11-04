import BuyAtBulk.Computation.PolynomialLP.Trace.Scalars
import BuyAtBulk.Computation.PolynomialLP.Trace.Dyadic

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace BuyAtBulk.PolynomialLP.Trace
open BuyAtBulk.Computation BuyAtBulk.Computation.Runtime
open Rational
variable {n : ℕ}

def inflation (n : ℕ) : Traced ℚ := do
  let d ← ratCast n
  let next ← ratAdd d 1
  let first ← ratMul 64 d
  let denominator ← ratMul first next
  let eta ← ratDiv 1 denominator
  let doubled ← ratMul 2 eta
  let base ← ratAdd 1 doubled
  ratMul base base
@[simp] theorem inflation_value (n : ℕ) : (inflation n).value = stepInflation n := by
  simp [inflation, stepInflation, stepEta, pow_two, ratCast, emit]
@[simp] theorem inflation_count (n : ℕ) : (inflation n).events.length = 15 := by
  simp [inflation, Traced.bind_events, List.length_append, ratCast, emit]

def diagonal (n precision : ℕ) : Traced ℚ := do
  let scale ← powerTwo precision
  let denominator ← ratCast scale
  let dimension ← ratCast n
  ratDiv dimension denominator
@[simp] theorem diagonal_value (n precision : ℕ) :
    (diagonal n precision).value = (n:ℚ)/(2:ℚ)^precision := by
  simp [diagonal, ratCast, emit]
@[simp] theorem diagonal_count (n precision : ℕ) :
    (diagonal n precision).events.length = 2*precision+5 := by
  simp [diagonal, Traced.bind_events, List.length_append, ratCast, emit, powerTwo_count]

def roundCenterCell (center : Vector ℚ n) (precision : ℕ) (i : Fin n) : Traced ℚ := do
  let q ← readRat center i
  dyadic q precision
@[simp] theorem roundCenterCell_value (center : Vector ℚ n) (precision : ℕ) (i : Fin n) :
    (roundCenterCell center precision i).value = (dyadicCode center[i.val] precision).value := by
  simp [roundCenterCell, dyadic_value, readRat]
@[simp] theorem roundCenterCell_count (center : Vector ℚ n) (precision : ℕ) (i : Fin n) :
    (roundCenterCell center precision i).events.length = 2*precision+14 := by
  simp [roundCenterCell, Traced.bind_events, List.length_append, dyadic_count, readRat, emit]

def roundShapeCell (shape : Vector (Vector ℚ n) n) (scale diagonal : ℚ)
    (precision : ℕ) (i j : Fin n) : Traced ℚ := do
  let row ← emit .read [i.val.size, n.size] shape[i.val]
  let q ← readRat row j
  let scaled ← ratMul scale q
  let rounded ← dyadic scaled precision
  let equal ← emit .natCompare [i.val.size, j.val.size] (decide (i=j))
  let extra ← emit .branch [1] (if equal then diagonal else 0)
  ratAdd rounded extra
@[simp] theorem roundShapeCell_value (shape : Vector (Vector ℚ n) n) (scale diag : ℚ)
    (precision : ℕ) (i j : Fin n) :
    (roundShapeCell shape scale diag precision i j).value =
      (dyadicCode (scale*shape[i.val][j.val]) precision).value+(if i=j then diag else 0) := by
  simp [roundShapeCell, dyadic_value, readRat]
@[simp] theorem roundShapeCell_count (shape : Vector (Vector ℚ n) n) (scale diag : ℚ)
    (precision : ℕ) (i j : Fin n) :
    (roundShapeCell shape scale diag precision i j).events.length = 2*precision+21 := by
  simp [roundShapeCell, Traced.bind_events, List.length_append, dyadic_count, readRat, emit]
  omega

def roundShape (shape : Vector (Vector ℚ n) n) (scale diag : ℚ) (precision : ℕ) :
    Traced (Vector (Vector ℚ n) n) :=
  Weights.materialize (fun i => Weights.materialize (roundShapeCell shape scale diag precision i)
    (fun q => (Code.ofRat q).bits)) (fun _ => n.size)

theorem roundShape_count (shape : Vector (Vector ℚ n) n) (scale diag : ℚ) (precision : ℕ) :
    (roundShape shape scale diag precision).events.length ≤ (2*precision+23)*n^2+3*n+1 := by
  have row (i : Fin n) := Weights.materialize_count (roundShapeCell shape scale diag precision i)
    (fun q => (Code.ofRat q).bits) (2*precision+21) (by intro j; simp)
  have all := Weights.materialize_count (fun i => Weights.materialize
    (roundShapeCell shape scale diag precision i) (fun q => (Code.ofRat q).bits))
    (fun _ => n.size) (n*(2*precision+23)+1) row
  dsimp only [roundShape]
  nlinarith

def roundedStep (state : Ellipsoid n) (direction : Vector ℚ n) (precision : ℕ) : Traced (Ellipsoid n) :=
  let center := rawCenter state direction
  let shape := rawShape state direction
  let scale := inflation n
  let diag := diagonal n precision
  let roundedCenter := Weights.materialize (roundCenterCell center.value precision) (fun q => (Code.ofRat q).bits)
  let roundedShape := roundShape shape.value scale.value diag.value precision
  ⟨⟨roundedCenter.value, roundedShape.value⟩,
    center.events ++ shape.events ++ scale.events ++ diag.events ++ roundedCenter.events ++
      roundedShape.events ++ [⟨.write, [n.size,n.size]⟩]⟩

theorem roundedStep_value (state : Ellipsoid n) (direction : Vector ℚ n) (precision : ℕ) :
    (roundedStep state direction precision).value = state.roundedStep direction precision := by
  simp only [roundedStep, Traced.bind_value, rawCenter_value, rawShape_value, inflation_value,
    diagonal_value, emit_value, Ellipsoid.roundedStep]
  congr 1
  · apply Vector.ext
    intro i bound
    change (Weights.materialize _ _).value[(⟨i,bound⟩ : Fin n).val] = _
    simp only [materialize_getNat, roundCenterCell_value, Vector.getElem_map]
  · apply Vector.ext
    intro i bound
    apply Vector.ext
    intro j boundj
    change (roundShape _ _ _ _).value[(⟨i,bound⟩ : Fin n).val][(⟨j,boundj⟩ : Fin n).val] = _
    simp only [roundShape, materialize_getNat, roundShapeCell_value, Vector.getElem_ofFn]

/-- A polynomial event budget in dimension, precision and the current quadratic
form's normalized encoding size. -/
def roundedStepBudget (n precision Q : ℕ) : ℕ :=
  (2*precision+100)*(n+1)^2+40*(Q+256*n*(n+1)+3)

theorem roundedStep_count (state : Ellipsoid n) (direction : Vector ℚ n) (precision : ℕ) :
    (roundedStep state direction precision).events.length ≤
      roundedStepBudget n precision (Code.ofRat (PolynomialLP.quadratic state.shape direction)).bits := by
  have c := rawCenter_count state direction
  have s := rawShape_count state direction
  have rc := Weights.materialize_count (roundCenterCell (state.rawCenter direction) precision)
    (fun q => (Code.ofRat q).bits) (2*precision+14) (by intro i; simp)
  have rs := roundShape_count (state.rawShape direction) (stepInflation n)
    ((n:ℚ)/(2:ℚ)^precision) precision
  simp only [roundedStep, Traced.bind_events, Traced.bind_value, List.length_append,
    rawCenter_value, rawShape_value, inflation_value, diagonal_value, inflation_count,
    diagonal_count, emit_length, roundedStepBudget, List.length_cons, List.length_nil]
  nlinarith

end BuyAtBulk.PolynomialLP.Trace
