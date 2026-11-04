import BuyAtBulk.Computation.PolynomialLP.Trace.Matrix

set_option autoImplicit false
set_option maxHeartbeats 300000
namespace BuyAtBulk.PolynomialLP.Trace
open BuyAtBulk.Computation BuyAtBulk.Computation.Runtime
variable {n m : ℕ}

def violated (input : Stored (n:=n) (m:=m)) (x : Vector ℚ n) (i : Fin m) : Traced Bool := do
  let a ← emit .read [i.val.size] input.coefficients[i.val]
  let columns ← indexList n
  let value ← dotScan a x columns
  let bound ← readRat input.bounds i
  ratLess bound value
@[simp] theorem violated_value (input : Stored (n:=n) (m:=m)) (x : Vector ℚ n) (i : Fin m) :
    (violated input x i).value = (PolynomialLP.violated input x i).value := by
  simp only [violated, PolynomialLP.violated, Traced.bind_value, emit_value, indexList_value, dot]
@[simp] theorem violated_count (input : Stored (n:=n) (m:=m)) (x : Vector ℚ n) (i : Fin m) :
    (violated input x i).events.length = 10*n+3 := by
  simp only [violated, Traced.bind_events, Traced.bind_value, List.length_append,
    emit_length, emit_value, indexList_count, indexList_value, dotScan_count,
    List.length_finRange, readRat, ratLess]
  omega

def separationScan (input : Stored (n:=n) (m:=m)) (x : Vector ℚ n) : List (Fin m) → Traced (Option (Fin m))
  | [] => Traced.pure none
  | i::rest => do
    let _ ← emit .scan [i.val.size] ()
    let test ← violated input x i
    let test ← branch test
    if test then Traced.pure (some i) else separationScan input x rest

theorem separationScan_value (input : Stored (n:=n) (m:=m)) (x : Vector ℚ n) (rows : List (Fin m)) :
    (separationScan input x rows).value = (PolynomialLP.separationScan input x rows).value := by
  induction rows with
  | nil => rfl
  | cons i rest ih =>
    simp only [separationScan, PolynomialLP.separationScan, Traced.bind_value,
      emit_value, violated_value, branch, Traced.ite_value]
    by_cases flag : (PolynomialLP.violated input x i).value = true <;> simp only [flag, Bool.false_eq_true, ite_false, if_pos, if_neg, ih]

theorem separationScan_count (input : Stored (n:=n) (m:=m)) (x : Vector ℚ n) (rows : List (Fin m)) :
    (separationScan input x rows).events.length ≤ (10*n+5)*rows.length := by
  induction rows with
  | nil => simp [separationScan, Traced.pure]
  | cons i rest ih =>
    simp only [separationScan, Traced.bind_events, Traced.bind_value, List.length_append,
      emit_length, emit_value, violated_count, branch, List.length_cons]
    by_cases flag : (violated input x i).value = true <;> simp only [flag, Bool.false_eq_true, ite_false, if_pos, if_neg, Traced.pure_events, List.length_nil] <;> nlinarith

def separate (input : Stored (n:=n) (m:=m)) (x : Vector ℚ n) : Traced (Option (Fin m)) := do
  let rows ← indexList m
  separationScan input x rows
@[simp] theorem separate_value (input : Stored (n:=n) (m:=m)) (x : Vector ℚ n) :
    (separate input x).value = (PolynomialLP.separate input x).value := by
  simp only [separate, Traced.bind_value, indexList_value, separationScan_value, PolynomialLP.separate]
theorem separate_count (input : Stored (n:=n) (m:=m)) (x : Vector ℚ n) :
    (separate input x).events.length ≤ (10*n+8)*m := by
  have count := separationScan_count input x (List.finRange m)
  simp only [separate, Traced.bind_events, Traced.bind_value, List.length_append,
    indexList_count, indexList_value]
  simp only [List.length_finRange] at count
  nlinarith

end BuyAtBulk.PolynomialLP.Trace
