import BuyAtBulk.Computation.Runtime.Logarithm
import BuyAtBulk.Computation.Runtime.HelperCoefficients
import BuyAtBulk.Computation.Runtime.SourceCoefficients
import BuyAtBulk.Computation.Runtime.Weights

/-! Coefficient construction with explicit ceiling-log and power schedules.
Tables are actually materialized into finite vectors. -/
namespace BuyAtBulk.Computation.Runtime.CoefficientPipeline
open Rational BuyAtBulk.UpperBound
variable {n h ratio m : ℕ}

def alpha (h : ℕ) : Traced ℚ := do
  let argument ← natMul 8 h
  let repetitions ← ceilingLog 2 argument (8*h)
  let rational ← ratCast repetitions
  ratMul 128 rational

theorem alpha_value (h : ℕ) : (alpha h).value = Core.helperAlpha h := by
  simp only [alpha, Traced.bind_value, natMul, emit_value,
    (helperLog_runtime h).1, ratCast, ratMul_value]
  rfl

theorem alpha_count (h : ℕ) : (alpha h).events.length ≤ 40*h+7 := by
  have log := (helperLog_runtime h).2
  simp only [alpha, Traced.bind_events, Traced.bind_value, natMul, emit_value, List.length_append,
    emit_length, ratCast, ratMul_length]
  omega

def isHeavy (opening : Vector ℚ n) (h : ℕ) (v : Fin n) : Traced Bool := do
  let a ← alpha h
  let x ← readRat opening v
  let product ← ratMul a x
  let test ← ratLe 1 product
  branch test

@[simp] theorem isHeavy_value (opening : Vector ℚ n) (h : ℕ) (v : Fin n) :
    (isHeavy opening h v).value = decide (1 ≤ Core.helperAlpha h*opening[v.val]) := by
  simp [isHeavy, Traced.bind_value, alpha_value, readRat, ratLe, branch]
  rfl

theorem isHeavy_count (opening : Vector ℚ n) (h : ℕ) (v : Fin n) :
    (isHeavy opening h v).events.length ≤ 40*h+12 := by
  have a := alpha_count h
  simp only [isHeavy, Traced.bind_events, Traced.bind_value, List.length_append,
    readRat, ratMul_length, ratLe, branch, emit_length]
  omega

def probability (opening : Vector ℚ n) (h : ℕ) (v : Fin n) : Traced ℚ := do
  let heavy ← isHeavy opening h v
  if heavy then Traced.pure 0 else do
    let a ← alpha h
    let x ← readRat opening v
    ratMul a x

theorem probability_value (opening : Vector ℚ n) (h : ℕ) (v : Fin n) :
    (probability opening h v).value = Core.helperProbability (fun v => opening[v.val]) h v := by
  simp only [probability, Traced.bind_value, isHeavy_value, Core.helperProbability,
    Traced.ite_value, decide_eq_true_eq, Traced.pure_value, alpha_value, readRat, emit_value, ratMul_value]

theorem probability_count (opening : Vector ℚ n) (h : ℕ) (v : Fin n) :
    (probability opening h v).events.length ≤ 80*h+22 := by
  have heavy := isHeavy_count opening h v
  have a := alpha_count h
  simp only [probability, Traced.bind_events, Traced.bind_value, List.length_append]
  split_ifs <;> simp only [Traced.pure_events, List.length_nil, Traced.bind_events, Traced.bind_value,
    List.length_append, readRat, emit_length, ratMul_length] <;> omega

def heavyScan (opening : Vector ℚ n) (h : ℕ) : List (Fin n) → Traced (List (Fin n))
  | [] => Traced.pure []
  | v::rest => do
      let _ ← emit .scan [v.val.size] ()
      let heavy ← isHeavy opening h v
      let tail ← heavyScan opening h rest
      if heavy then emit .cons [v.val.size] (v::tail) else Traced.pure tail

theorem heavyScan_value (opening : Vector ℚ n) (h : ℕ) (vertices : List (Fin n)) :
    (heavyScan opening h vertices).value = vertices.filter (fun v => decide (1 ≤ Core.helperAlpha h*opening[v.val])) := by
  induction vertices with
  | nil => rfl
  | cons v rest ih =>
    simp only [heavyScan, Traced.bind_value, emit_value, isHeavy_value, ih]
    split_ifs <;> simp_all [List.filter_cons]

theorem heavyScan_count (opening : Vector ℚ n) (h : ℕ) (vertices : List (Fin n)) :
    (heavyScan opening h vertices).events.length ≤ (40*h+14)*vertices.length := by
  induction vertices with
  | nil => simp [heavyScan, Traced.pure]
  | cons v rest ih =>
    have heavy := isHeavy_count opening h v
    simp only [heavyScan, Traced.bind_events, Traced.bind_value, emit_value, List.length_append,
      emit_length, List.length_cons]
    split_ifs <;> simp only [emit_length, Traced.pure_events, List.length_nil] <;> nlinarith

def amplitude (opening : Vector ℚ n) (database : Core.RowDatabase h ratio n) (row : Core.RawRow h ratio) : Traced ℚ := do
  let vertices ← indexList n
  let heavy ← heavyScan opening h vertices
  let sum ← Runtime.weightedTolls opening database row heavy
  let data ← Runtime.getRow database row
  let radius ← emit .read [(Code.ofRat data.radius).bits] data.radius
  let thresholdNumerator ← ratMul 3 radius
  let threshold ← ratDiv thresholdNumerator 8
  let light ← ratLess sum threshold
  let light ← branch light
  if light then do
    let argument ← natMul 8 h
    let repetitions ← ceilingLog 2 argument (8*h)
    let exponent ← natMul 16 repetitions
    let power ← powerTwo exponent
    ratCast power
  else Traced.pure 0

theorem amplitude_value (opening : Vector ℚ n) (database : Core.RowDatabase h ratio n) (row : Core.RawRow h ratio) :
    (amplitude opening database row).value = Core.helperAmplitude (Equiv.refl _) (fun v => opening[v.val]) database row := by
  simp only [amplitude, Traced.bind_value, indexList_value, heavyScan_value, Runtime.weightedTolls_value, Runtime.getRow,
    ratMul_value, ratDiv_value, ratLess, branch, emit_value]
  simp only [Core.helperAmplitude, Core.heavyVertices, Core.vertexOrder, List.map_id_fun,
    Equiv.refl_symm, Equiv.coe_refl, Core.storedToll, Core.helperRepetitions, Equiv.refl_apply]
  simp only [Traced.ite_value, decide_eq_true_eq, Traced.pure_value, Traced.bind_value,
    natMul, emit_value, (helperLog_runtime h).1, powerTwo_value, ratCast,
    Nat.cast_pow, Nat.cast_ofNat]
  simp [Traced.bind, Traced.pure, emit, Nat.cast_pow, (helperLog_runtime h).1]

theorem amplitude_count (opening : Vector ℚ n) (database : Core.RowDatabase h ratio n) (row : Core.RawRow h ratio) :
    (amplitude opening database row).events.length ≤ (40*h+28)*n+296*h+18 := by
  have heavy := heavyScan_count opening h (List.finRange n)
  have length : (heavyScan opening h (List.finRange n)).value.length ≤ n := by
    rw [heavyScan_value]
    simpa using List.length_filter_le (fun v : Fin n => decide (1 ≤ Core.helperAlpha h*opening[v.val])) (List.finRange n)
  have weighted := Runtime.weightedTolls_count opening database row (heavyScan opening h (List.finRange n)).value
  have log := (helperLog_runtime h).2
  have power := (helperPower_runtime h).2.1
  simp only [List.length_finRange] at heavy
  simp only [amplitude, Traced.bind_events, Traced.bind_value, indexList_value, indexList_count, emit_value, List.length_append,
    Runtime.getRow, ratMul_length, ratDiv_length, ratLess, branch, emit_length]
  split_ifs <;> simp only [Traced.pure_events, List.length_nil, Traced.bind_events, Traced.bind_value,
    List.length_append, natMul, emit_length, emit_value, (helperLog_runtime h).1, ratCast]
  all_goals simp_all only [ite_true, ite_false, Bool.false_eq_true, Traced.pure_events,
    Traced.bind_events, Traced.bind_value, List.length_append, List.length_cons, List.length_nil,
    natMul, emit_length, emit_value, (helperLog_runtime h).1, ratCast]
  all_goals nlinarith

end BuyAtBulk.Computation.Runtime.CoefficientPipeline
