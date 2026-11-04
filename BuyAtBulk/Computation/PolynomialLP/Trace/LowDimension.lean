import BuyAtBulk.Computation.PolynomialLP.LowDimension
import BuyAtBulk.Computation.PolynomialLP.Trace.Separation

set_option autoImplicit false
set_option maxHeartbeats 600000
namespace BuyAtBulk.PolynomialLP.Trace
open BuyAtBulk.Computation BuyAtBulk.Computation.Runtime
variable {m : ℕ}

def writeInterval (interval : Interval) : Traced Interval :=
  emit .write [1,(Rational.Code.ofRat interval.lower).bits,(Rational.Code.ofRat interval.upper).bits] interval
@[simp] theorem writeInterval_value (interval : Interval) : (writeInterval interval).value = interval := rfl
@[simp] theorem writeInterval_count (interval : Interval) : (writeInterval interval).events.length = 1 := rfl

def cut (interval : Interval) (a b : ℚ) : Traced Interval := do
  let zero ← emit .ratCompare [(Rational.Code.ofRat a).bits] (decide (a=0))
  let zero ← branch zero
  if zero then do
    let positive ← ratLe 0 b
    let positive ← branch positive
    writeInterval (if positive then interval else ⟨1,0⟩)
  else do
    let positive ← ratLess 0 a
    let positive ← branch positive
    let endpoint ← ratDiv b a
    if positive then do
      let less ← ratLe interval.upper endpoint
      let less ← branch less
      writeInterval ⟨interval.lower, if less then interval.upper else endpoint⟩
    else do
      let less ← ratLe interval.lower endpoint
      let less ← branch less
      writeInterval ⟨if less then endpoint else interval.lower, interval.upper⟩

theorem cut_value (interval : Interval) (a b : ℚ) : (cut interval a b).value = interval.cut a b := by
  simp only [cut, Traced.bind_value, emit_value, branch, Interval.cut, writeInterval_value]
  by_cases zero : a=0
  · simp only [zero, decide_true, Bool.true_eq, if_pos, Traced.bind_value, ratLe, emit_value, branch]
    split_ifs <;> simp_all
  · simp only [zero, decide_false, Bool.false_eq_true, if_neg, Traced.bind_value, ratLess,
      emit_value, branch, ratDiv_value, ratLe]
    by_cases positive : 0<a
    · simp only [positive, decide_true, Bool.true_eq, if_pos, Traced.bind_value, ratLe, emit_value, branch]
      by_cases le : interval.upper ≤ b/a <;> simp [le, min_def]
    · simp only [positive, decide_false, Bool.false_eq_true, if_neg, Traced.bind_value, ratLe, emit_value, branch]
      by_cases le : interval.lower ≤ b/a <;> simp [le, max_def]

theorem cut_count (interval : Interval) (a b : ℚ) : (cut interval a b).events.length ≤ 9 := by
  simp only [cut, Traced.bind_events, Traced.bind_value, emit_length, emit_value, branch]
  by_cases zero : a=0
  · simp [zero, Traced.bind_events, List.length_append, ratLe, emit, branch, writeInterval]
  · simp only [zero, decide_false, Bool.false_eq_true, ite_false, Traced.bind_events,
      Traced.bind_value, ratLess, emit_length, emit_value, branch, ratDiv_length, ratDiv_value,
      List.length_append]
    by_cases positive : 0<a <;>
      simp [positive, Traced.bind_events, List.length_append, ratLe, emit, branch, writeInterval]

def intervalScan (input : Stored (n:=1) (m:=m)) : List (Fin m) → Interval → Traced Interval
  | [], interval => Traced.pure interval
  | i::rest, interval => do
    let _ ← emit .scan [i.val.size] ()
    let row ← emit .read [i.val.size] input.coefficients[i.val]
    let a ← readRat row 0
    let b ← readRat input.bounds i
    let next ← cut interval a b
    intervalScan input rest next

theorem intervalScan_value (input : Stored (n:=1) (m:=m)) (rows : List (Fin m)) (interval : Interval) :
    (intervalScan input rows interval).value = PolynomialLP.intervalScan input rows interval := by
  induction rows generalizing interval with
  | nil => rfl
  | cons i rest ih =>
    simp only [intervalScan, Traced.bind_value, emit_value, readRat, cut_value, ih,
      PolynomialLP.intervalScan, Fin.val_zero]

theorem intervalScan_count (input : Stored (n:=1) (m:=m)) (rows : List (Fin m)) (interval : Interval) :
    (intervalScan input rows interval).events.length ≤ 13*rows.length := by
  induction rows generalizing interval with
  | nil => simp [intervalScan, Traced.pure]
  | cons i rest ih =>
    have c := cut_count interval input.coefficients[i.val][0] input.bounds[i.val]
    have r := ih (interval.cut input.coefficients[i.val][0] input.bounds[i.val])
    simp only [intervalScan, Traced.bind_events, Traced.bind_value, emit_length, emit_value,
      readRat, List.length_append, cut_value, List.length_cons, Fin.val_zero]
    omega

def unarySolve (input : Stored (n:=1) (m:=m)) : Traced (Option ℚ) := do
  let rows ← indexList m
  let interval ← intervalScan input rows ⟨0,1⟩
  let valid ← ratLe interval.lower interval.upper
  let valid ← branch valid
  if valid then do
    let coefficient ← readRat input.objective 0
    let negative ← ratLess coefficient 0
    let negative ← branch negative
    let endpoint := if negative then interval.upper else interval.lower
    emit .write [1,(Rational.Code.ofRat endpoint).bits] (some endpoint)
  else emit .write [1] none

theorem unarySolve_value (input : Stored (n:=1) (m:=m)) :
    (unarySolve input).value = PolynomialLP.unarySolve input := by
  simp only [unarySolve, Traced.bind_value, indexList_value, intervalScan_value,
    PolynomialLP.unarySolve, unaryInterval, ratLe, emit_value, branch]
  by_cases valid : (PolynomialLP.unaryInterval input).lower ≤ (PolynomialLP.unaryInterval input).upper
  · simp only [unaryInterval] at valid
    simp only [valid, decide_true, Bool.true_eq, if_pos, Traced.bind_value, readRat, ratLess, emit_value, branch]
    simp only [Fin.val_zero]
    by_cases negative : input.objective[0]<0 <;> simp [negative]
  · simp only [unaryInterval] at valid
    simp only [valid, decide_false, Bool.false_eq_true, if_neg, ite_false, emit_value]

theorem unarySolve_count (input : Stored (n:=1) (m:=m)) :
    (unarySolve input).events.length ≤ 16*m+6 := by
  have scan := intervalScan_count input (List.finRange m) ⟨0,1⟩
  simp only [unarySolve, Traced.bind_events, Traced.bind_value, List.length_append,
    indexList_count, indexList_value, ratLe, emit_length, emit_value, branch]
  by_cases valid : (intervalScan input (List.finRange m) ⟨0,1⟩).value.lower ≤
      (intervalScan input (List.finRange m) ⟨0,1⟩).value.upper <;>
    simp [valid, Traced.bind_events, List.length_append, readRat, ratLess, emit, branch]
  all_goals simp only [List.length_finRange] at scan; omega

def zeroSolve (input : Stored (n:=0) (m:=m)) : Traced (Option (Vector ℚ 0)) := do
  let point ← emit .write [1] (Vector.replicate 0 (0:ℚ))
  let result ← separate input point
  let result ← emit .branch [1] result
  emit .write [1] (match result with | none => some point | some _ => none)

theorem zeroSolve_value (input : Stored (n:=0) (m:=m)) :
    (zeroSolve input).value = PolynomialLP.zeroSolve input := by
  simp only [zeroSolve, Traced.bind_value, emit_value, separate_value, PolynomialLP.zeroSolve]
  cases (PolynomialLP.separate input (Vector.replicate 0 0)).value <;> rfl

theorem zeroSolve_count (input : Stored (n:=0) (m:=m)) :
    (zeroSolve input).events.length ≤ 8*m+3 := by
  have scan := separate_count input (Vector.replicate 0 0)
  simp only [zeroSolve, Traced.bind_events, Traced.bind_value, List.length_append,
    emit_length, emit_value]
  omega

end BuyAtBulk.PolynomialLP.Trace
