import BuyAtBulk.Computation.Runtime.Primitive
import BuyAtBulk.Computation.Core.Initialization

/-! Instrumentation of the helper's coefficient callbacks. In particular,
alpha is recomputed on each callback and each scan; it is not a free oracle. -/
namespace BuyAtBulk.Computation.Runtime
open BuyAtBulk.UpperBound
variable {n h ratio : ℕ}

def alpha (h : ℕ) : Traced ℚ := do
  let argument ← natMul 8 h
  let repetitions ← natClog 2 argument
  let rational ← ratCast repetitions
  ratMul 128 rational

@[simp] theorem alpha_value (h : ℕ) : (alpha h).value = Core.helperAlpha h := rfl
@[simp] theorem alpha_count (h : ℕ) : (alpha h).events.length = 5 := rfl

def isHeavy (opening : Vector ℚ n) (h : ℕ) (v : Fin n) : Traced Bool := do
  let a ← alpha h
  let x ← readRat opening v
  let product ← ratMul a x
  let test ← ratLe 1 product
  branch test

@[simp] theorem isHeavy_value (opening : Vector ℚ n) (h : ℕ) (v : Fin n) :
    (isHeavy opening h v).value = decide (1 ≤ Core.helperAlpha h * opening[v.val]) := rfl
@[simp] theorem isHeavy_count (opening : Vector ℚ n) (h : ℕ) (v : Fin n) :
    (isHeavy opening h v).events.length = 10 := rfl

def heavyScan (opening : Vector ℚ n) (h : ℕ) : List (Fin n) → Traced (List (Fin n))
  | [] => Traced.pure []
  | v :: rest => do
      let _ ← emit .scan [v.val.size] ()
      let test ← isHeavy opening h v
      let tail ← heavyScan opening h rest
      if test then emit .cons [v.val.size] (v :: tail) else Traced.pure tail

theorem heavyScan_value (opening : Vector ℚ n) (h : ℕ) (vertices : List (Fin n)) :
    (heavyScan opening h vertices).value =
      vertices.filter (fun v => decide (1 ≤ Core.helperAlpha h * opening[v.val])) := by
  induction vertices with
  | nil => rfl
  | cons v rest ih =>
    simp only [heavyScan, Traced.bind_value, emit_value, isHeavy_value, ih]
    split_ifs <;> simp_all [List.filter_cons]

theorem heavyScan_count (opening : Vector ℚ n) (h : ℕ) (vertices : List (Fin n)) :
    (heavyScan opening h vertices).events.length ≤ 12 * vertices.length := by
  induction vertices with
  | nil => simp [heavyScan, Traced.pure]
  | cons v rest ih =>
    simp only [heavyScan, Traced.bind_events, Traced.bind_value, emit_value, List.length_append,
      emit_length, isHeavy_count, List.length_cons]
    split_ifs <;> simp only [emit_length, Traced.pure_events, List.length_nil] <;> omega

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
    (probability opening h v).events.length ≤ 18 := by
  simp only [probability, Traced.bind_events, Traced.bind_value, isHeavy_count, List.length_append]
  split_ifs <;> simp [Traced.bind_events, Traced.bind_value, Traced.pure, alpha_count,
    readRat, ratMul_length, List.length_append]

def getRow (database : Core.RowDatabase h ratio n) (raw : Core.RawRow h ratio) : Traced (Core.RowValues n) :=
  ⟨Core.getRow database raw,
    [⟨.index, [raw.1.val.size]⟩, ⟨.branch, [1]⟩, ⟨.index, [1]⟩, ⟨.index, [raw.2.2.val.size]⟩]⟩

def factor (database : Core.RowDatabase h ratio n) (raw : Core.RawRow h ratio) (v : Fin n) : Traced ℚ := do
  let first ← getRow database raw
  let toll ← readRat first.toll v
  let second ← getRow database raw
  let denominator ← ratMul 2 second.radius
  let quotient ← ratDiv toll denominator
  let negative ← emit .ratNeg [(Rational.Code.ofRat quotient).bits] (-quotient)
  ratAdd 1 negative

theorem factor_value (database : Core.RowDatabase h ratio n) (raw : Core.RawRow h ratio) (v : Fin n) :
    (factor database raw v).value = Core.helperFactor (Equiv.refl _) database raw v := by
  simp only [factor, Traced.bind_value, getRow, readRat, emit_value, ratMul_value, ratDiv_value, ratAdd_value,
    Core.helperFactor, Core.storedToll, Equiv.refl_apply]
  ring

theorem factor_count (database : Core.RowDatabase h ratio n) (raw : Core.RawRow h ratio) (v : Fin n) :
    (factor database raw v).events.length = 16 := rfl

def weightedTolls (opening : Vector ℚ n) (database : Core.RowDatabase h ratio n) (raw : Core.RawRow h ratio) :
    List (Fin n) → Traced ℚ
  | [] => Traced.pure 0
  | v :: rest => do
      let _ ← emit .scan [v.val.size] ()
      let x ← readRat opening v
      let row ← getRow database raw
      let toll ← readRat row.toll v
      let term ← ratMul x toll
      let tail ← weightedTolls opening database raw rest
      ratAdd term tail

theorem weightedTolls_value (opening : Vector ℚ n) (database : Core.RowDatabase h ratio n)
    (raw : Core.RawRow h ratio) (vertices : List (Fin n)) :
    (weightedTolls opening database raw vertices).value =
      (vertices.map fun v => opening[v.val] * (Core.getRow database raw).toll[v.val]).sum := by
  induction vertices with
  | nil => rfl
  | cons v rest ih =>
    simp only [weightedTolls, Traced.bind_value, emit_value, readRat, getRow, ratMul_value,
      ratAdd_value, ih, List.map_cons, List.sum_cons]

theorem weightedTolls_count (opening : Vector ℚ n) (database : Core.RowDatabase h ratio n)
    (raw : Core.RawRow h ratio) (vertices : List (Fin n)) :
    (weightedTolls opening database raw vertices).events.length = 11 * vertices.length := by
  induction vertices with
  | nil => rfl
  | cons v rest ih =>
    simp only [weightedTolls, Traced.bind_events, Traced.bind_value, emit_value, List.length_append,
      emit_length, readRat, getRow, ratMul_length, ratAdd_length, ih, List.length_cons]
    simp only [List.length_cons, List.length_nil]
    omega

def amplitude (opening : Vector ℚ n) (database : Core.RowDatabase h ratio n) (raw : Core.RawRow h ratio) : Traced ℚ := do
  let heavy ← heavyScan opening h (List.finRange n)
  let sum ← weightedTolls opening database raw heavy
  let row ← getRow database raw
  let threeRadius ← ratMul 3 row.radius
  let threshold ← ratDiv threeRadius 8
  let light ← ratLess sum threshold
  let light ← branch light
  if light then do
    let argument ← natMul 8 h
    let repetitions ← natClog 2 argument
    let exponent ← natMul 16 repetitions
    let power ← natPower 2 exponent
    ratCast power
  else Traced.pure 0

theorem amplitude_value (opening : Vector ℚ n) (database : Core.RowDatabase h ratio n)
    (raw : Core.RawRow h ratio) :
    (amplitude opening database raw).value =
      Core.helperAmplitude (Equiv.refl _) (fun v => opening[v.val]) database raw := by
  simp only [amplitude, Traced.bind_value, heavyScan_value, weightedTolls_value, getRow,
    ratMul_value, ratDiv_value, ratLess, branch, emit_value]
  simp only [Core.helperAmplitude, Core.heavyVertices, Core.vertexOrder, List.map_id_fun,
    Equiv.refl_symm, Equiv.coe_refl, Core.storedToll, Core.helperRepetitions, Equiv.refl_apply]
  simp only [Traced.ite_value, decide_eq_true_eq, Traced.pure_value, Traced.bind_value,
    natMul, natClog, natPower, ratCast, emit_value, Nat.cast_pow, Nat.cast_ofNat]
  simp [Traced.bind, Traced.pure, emit, Nat.cast_pow]

theorem amplitude_count (opening : Vector ℚ n) (database : Core.RowDatabase h ratio n)
    (raw : Core.RawRow h ratio) :
    (amplitude opening database raw).events.length ≤ 23 * n + 15 := by
  have scan := heavyScan_count opening h (List.finRange n)
  have length : (heavyScan opening h (List.finRange n)).value.length ≤ n := by
    rw [heavyScan_value]
    exact (List.length_filter_le _ _).trans_eq List.length_finRange
  simp only [List.length_finRange] at scan
  simp only [amplitude, Traced.bind_events, Traced.bind_value, List.length_append,
    weightedTolls_count, getRow, ratMul_length, ratDiv_length, ratLess, branch, emit_length]
  split_ifs <;> simp only [Traced.pure_events, List.length_nil, List.length_cons,
    Traced.bind_events, Traced.bind_value, natMul, natClog, natPower, ratCast, emit_length, List.length_append] <;>
    change _ ≤ _ <;> omega

end BuyAtBulk.Computation.Runtime
