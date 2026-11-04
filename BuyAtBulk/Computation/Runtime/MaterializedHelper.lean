import BuyAtBulk.Computation.Runtime.CoefficientPipeline
import BuyAtBulk.Computation.Runtime.CachedHelper

namespace BuyAtBulk.Computation.Runtime.MaterializedHelper
open Rational BuyAtBulk.UpperBound
variable {n h ratio m : ℕ}

def buyingSum (buying : Vector ℚ n) : List (Fin n) → Traced ℚ
  | [] => Traced.pure 0
  | v::rest => do
      let _ ← emit .scan [v.val.size] ()
      let q ← readRat buying v
      let tail ← buyingSum buying rest
      ratAdd q tail

@[simp] theorem buyingSum_value (buying : Vector ℚ n) (vertices : List (Fin n)) :
    (buyingSum buying vertices).value=(vertices.map fun v => buying[v.val]).sum := by
  induction vertices with
  | nil => rfl
  | cons v rest ih => simp [buyingSum,Traced.bind_value,readRat,ih]

@[simp] theorem buyingSum_count (buying : Vector ℚ n) (vertices : List (Fin n)) :
    (buyingSum buying vertices).events.length=4*vertices.length := by
  induction vertices with
  | nil => rfl
  | cons v rest ih =>
    simp only [buyingSum,Traced.bind_events,Traced.bind_value,emit_length,emit_value,readRat,
      List.length_append,ratAdd_length,List.length_cons,ih]
    omega

def fixedCost (buying opening : Vector ℚ n) (h : ℕ) : Traced ℚ := do
  let indices ← indexList n
  let heavy ← CoefficientPipeline.heavyScan opening h indices
  buyingSum buying heavy

@[simp] theorem fixedCost_value (buying opening : Vector ℚ n) (h : ℕ) :
    (fixedCost buying opening h).value=Core.helperFixedCost (Equiv.refl _) (fun v => buying[v.val]) (fun v => opening[v.val]) h := by
  simp [fixedCost,Traced.bind_value,CoefficientPipeline.heavyScan_value,Core.helperFixedCost,
    Core.heavyVertices,Core.vertexOrder]

theorem fixedCost_count (buying opening : Vector ℚ n) (h : ℕ) :
    (fixedCost buying opening h).events.length≤(40*h+21)*n := by
  have heavy := CoefficientPipeline.heavyScan_count opening h (List.finRange n)
  have length : (CoefficientPipeline.heavyScan opening h (List.finRange n)).value.length≤n := by
    rw [CoefficientPipeline.heavyScan_value]
    simpa using List.length_filter_le (fun v : Fin n => decide (1≤Core.helperAlpha h*opening[v.val])) (List.finRange n)
  simp only [fixedCost,Traced.bind_events,Traced.bind_value,List.length_append,indexList_count,indexList_value,buyingSum_count]
  simp only [List.length_finRange] at heavy
  nlinarith

def normalization (budget : ℚ) (h : ℕ) : Traced ℚ := do
  let alpha ← CoefficientPipeline.alpha h
  let four ← ratMul 4 alpha
  ratMul four budget

@[simp] theorem normalization_value (budget : ℚ) (h : ℕ) :
    (normalization budget h).value=4*Core.helperAlpha h*budget := by
  simp [normalization,Traced.bind_value,CoefficientPipeline.alpha_value]

theorem normalization_count (budget : ℚ) (h : ℕ) :
    (normalization budget h).events.length≤40*h+11 := by
  have alpha := CoefficientPipeline.alpha_count h
  simp only [normalization,Traced.bind_events,Traced.bind_value,List.length_append,ratMul_length]
  omega

def factor (database : Core.RowDatabase h ratio n) (raw : Core.RawRow h ratio) (v : Fin n) : Traced ℚ := do
  let data ← Runtime.getRow database raw
  let toll ← readRat data.toll v
  let radius ← emit .read [(Code.ofRat data.radius).bits] data.radius
  let denominator ← ratMul 2 radius
  let quotient ← ratDiv toll denominator
  let negative ← emit .ratNeg [(Code.ofRat quotient).bits,(Code.ofRat (-quotient)).bits] (-quotient)
  ratAdd 1 negative

@[simp] theorem factor_value (database : Core.RowDatabase h ratio n) (raw : Core.RawRow h ratio) (v : Fin n) :
    (factor database raw v).value=Core.helperFactor (Equiv.refl _) database raw v := by
  simp [factor,Traced.bind_value,Runtime.getRow,readRat,Core.helperFactor,Core.storedToll,sub_eq_add_neg]

@[simp] theorem factor_count (database : Core.RowDatabase h ratio n) (raw : Core.RawRow h ratio) (v : Fin n) :
    (factor database raw v).events.length=13 := by
  simp [factor,Traced.bind_events,Runtime.getRow,readRat,List.length_append]

def factors (database : Core.RowDatabase h ratio n) (rows : Vector (Core.RawRow h ratio) m) :
    Traced (Vector (Vector ℚ n) m) :=
  Weights.materialize (fun r => do
    let raw ← emit .read [r.val.size] rows[r.val]
    Weights.materialize (factor database raw) (fun q => (Code.ofRat q).bits)) (fun _ => n.size)

def amplitudes (opening : Vector ℚ n) (database : Core.RowDatabase h ratio n) (rows : Vector (Core.RawRow h ratio) m) :
    Traced (Vector ℚ m) :=
  Weights.materialize (fun r => do
    let raw ← emit .read [r.val.size] rows[r.val]
    CoefficientPipeline.amplitude opening database raw) (fun q => (Code.ofRat q).bits)

def tables (buying opening : Vector ℚ n) (budget : ℚ)
    (database : Core.RowDatabase h ratio n) (rows : Vector (Core.RawRow h ratio) m) :
    Traced (HelperConstruction.StoredTables n m) :=
  let order := indexList m
  let probability := Weights.materialize (CoefficientPipeline.probability opening h) (fun q => (Code.ofRat q).bits)
  let factor := factors database rows
  let amplitude := amplitudes opening database rows
  let fixed := fixedCost buying opening h
  let norm := normalization budget h
  ⟨{ buying := buying
     probability := probability.value
     factor := factor.value
     amplitude := amplitude.value
     fixedCost := fixed.value
     normalization := norm.value
     rowOrder := order.value
     rowOrder_eq := indexList_value m },
   order.events++probability.events++factor.events++amplitude.events++fixed.events++norm.events++
     [⟨.write,[n.size,m.size]⟩]⟩

@[simp] theorem factors_get (database : Core.RowDatabase h ratio n) (rows : Vector (Core.RawRow h ratio) m)
    (r : Fin m) (v : Fin n) : (factors database rows).value[r.val][v.val]=
      Core.helperFactor (Equiv.refl _) database rows[r.val] v := by
  simp [factors,Weights.materialize_get,Traced.bind_value,factor_value]

@[simp] theorem amplitudes_get (opening : Vector ℚ n) (database : Core.RowDatabase h ratio n)
    (rows : Vector (Core.RawRow h ratio) m) (r : Fin m) :
    (amplitudes opening database rows).value[r.val]=
      Core.helperAmplitude (Equiv.refl _) (fun v => opening[v.val]) database rows[r.val] := by
  simp [amplitudes,Weights.materialize_get,Traced.bind_value,CoefficientPipeline.amplitude_value]

theorem tables_value (buying opening : Vector ℚ n) (budget : ℚ)
    (database : Core.RowDatabase h ratio n) (rows : Vector (Core.RawRow h ratio) m) :
    (tables buying opening budget database rows).value=SourceCoefficients.tables buying opening budget database rows := by
  simp only [tables,Traced.bind_value,emit_value,indexList_value,fixedCost_value,normalization_value]
  congr 1
  · apply Vector.ext
    intro i hi
    simp [Weights.materialize,CoefficientPipeline.probability_value,SourceCoefficients.tables]
  · apply Vector.ext
    intro i hi
    apply Vector.ext
    intro j hj
    simpa [SourceCoefficients.tables] using factors_get database rows ⟨i,hi⟩ ⟨j,hj⟩
  · apply Vector.ext
    intro i hi
    simpa [SourceCoefficients.tables] using amplitudes_get opening database rows ⟨i,hi⟩

theorem factors_count (database : Core.RowDatabase h ratio n) (rows : Vector (Core.RawRow h ratio) m) :
    (factors database rows).events.length≤m*(15*n+4)+1 := by
  have inner (r : Fin m) := Weights.materialize_count (factor database rows[r.val]) (fun q => (Code.ofRat q).bits)
    13 (fun v => by simp)
  apply Weights.materialize_count
  intro r
  have bound := inner r
  simp only [Traced.bind_events,Traced.bind_value,emit_length,emit_value,List.length_append]
  omega

theorem amplitudes_count (opening : Vector ℚ n) (database : Core.RowDatabase h ratio n)
    (rows : Vector (Core.RawRow h ratio) m) :
    (amplitudes opening database rows).events.length≤m*((40*h+28)*n+296*h+21)+1 := by
  apply Weights.materialize_count
  intro r
  have bound := CoefficientPipeline.amplitude_count opening database rows[r.val]
  simp only [Traced.bind_events,Traced.bind_value,emit_length,emit_value,List.length_append]
  omega

def tableCount (n h m : ℕ) : ℕ :=
  3*m+n*(80*h+24)+m*(15*n+4)+m*((40*h+28)*n+296*h+21)+(40*h+21)*n+40*h+15

theorem tables_count (buying opening : Vector ℚ n) (budget : ℚ)
    (database : Core.RowDatabase h ratio n) (rows : Vector (Core.RawRow h ratio) m) :
    (tables buying opening budget database rows).events.length≤tableCount n h m := by
  have probability := Weights.materialize_count (CoefficientPipeline.probability opening h) (fun q => (Code.ofRat q).bits)
    (80*h+22) (CoefficientPipeline.probability_count opening h)
  have fs := factors_count database rows
  have amps := amplitudes_count opening database rows
  have fixed := fixedCost_count buying opening h
  have norm := normalization_count budget h
  simp only [tables,List.length_append,List.length_cons,List.length_nil,indexList_count]
  dsimp only [tableCount]
  nlinarith

end BuyAtBulk.Computation.Runtime.MaterializedHelper
