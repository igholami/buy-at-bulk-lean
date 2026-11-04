import BuyAtBulk.Computation.Runtime.CoreTollWords

namespace BuyAtBulk.Computation.Runtime.StoredCore
open BuyAtBulk.UpperBound
open Rational
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

def rowWidth (row : Core.RowValues n) : ℕ :=
  (Code.ofRat row.radius).bits+1+((List.finRange n).map fun v => (Code.ofRat row.toll[v.val]).bits).sum

def castDatabase {d e : ℕ} (same : d=e) (rows : Vector (Vector (Vector (Core.RowValues n) d) 2) h) :
    Vector (Vector (Vector (Core.RowValues n) e) 2) h :=
  cast (congrArg (fun k => Vector (Vector (Vector (Core.RowValues n) k) 2) h) same) rows

@[simp] theorem castDatabase_get {d e : ℕ} (same : d=e) (rows : Vector (Vector (Vector (Core.RowValues n) d) 2) h)
    (i : ℕ) (hi : i<h) (s : ℕ) (hs : s<2) (j : ℕ) (hj : j<e) :
    (castDatabase same rows)[i][s][j] = rows[i][s][j]'(by omega) := by
  subst e
  rfl

def materializeRows (buying physical : Vector ℚ n) (budget : ℚ) (allowance : Vector ℚ h)
    (source target : Vector (Fin n) h) (ratio : ℕ) (ratio_ge : 2 ≤ ratio) : Traced (Core.RowDatabase h ratio n) :=
  let D := StoredServe.gridDepth h ratio
  have depth_eq : D.value+1 = UpperBound.gridDepth h ratio+1 := congrArg (·+1) (StoredServe.gridDepth_value h ratio ratio_ge)
  let rows := Weights.materialize (fun i : Fin h =>
    Weights.materialize (fun side : Fin 2 =>
      Weights.materialize (fun depth : Fin (D.value+1) =>
        materializeRow input buying physical budget allowance source target ratio
          (i, decide (side.val=1), depth.cast depth_eq)) rowWidth)
      (fun cells => ((List.finRange (D.value+1)).map fun d => rowWidth cells[d.val]).sum))
    (fun sides => ((List.finRange 2).map fun side =>
      ((List.finRange (D.value+1)).map fun d => rowWidth sides[side.val][d.val]).sum).sum)
  ⟨castDatabase depth_eq rows.value,
    D.events ++ rows.events⟩

theorem materializeRows_value (buying physical : Vector ℚ n) (budget : ℚ) (allowance : Vector ℚ h)
    (source target : Vector (Fin n) h) (ratio : ℕ) (ratio_ge : 2 ≤ ratio) :
    (materializeRows input buying physical budget allowance source target ratio ratio_ge).value =
      Core.materializeRows input.graph (Equiv.refl _) (fun v => buying[v.val]) (fun v => physical[v.val]) budget
        (fun i => allowance[i.val]) (fun i => source[i.val]) (fun i => target[i.val]) ratio := by
  simp only [materializeRows, StoredServe.gridDepth_value h ratio ratio_ge, Fin.cast_refl]
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro side hs
  apply Vector.ext
  intro d hd
  simp only [castDatabase_get, Weights.materialize, Vector.getElem_map, Vector.getElem_ofFn, Core.materializeRows]
  exact materializeRow_value input buying physical budget allowance source target ratio _

theorem emptyState_count : (emptyState input).events.length ≤ 3*n+2 := by
  have cells := Weights.materialize_count (fun _ : Fin n => emit .write [1] false) (fun _ => 1) 1 (by intro; rfl)
  simp only [emptyState, List.length_append, List.length_cons, List.length_nil] at *
  omega

theorem rowFromDistances_count (buying : Vector ℚ n) (radius : ℚ) (mate : Fin n) (distances : Vector (WithTop ℚ) n) :
    (rowFromDistances buying radius mate distances).events.length ≤ 14*n+5 := by
  have cells := Weights.materialize_count (fun v : Fin n => do
    let buy ← readRat buying v
    let label ← Runtime.ShortestPath.read distances v
    tollFromLabel buy radius label) (fun q : ℚ => (Code.ofRat q).bits) 12 (by
      intro v
      have actual := tollFromLabel_count buying[v.val] radius distances[v.val]
      simp only [Traced.bind_events, Traced.bind_value, List.length_append, readRat, Runtime.ShortestPath.read,
        emit_value, emit_length]
      omega)
  simp only [rowFromDistances, Traced.bind_events, Traced.bind_value, List.length_append, emit_length,
    Runtime.ShortestPath.read, ratLess, emit_value] at *
  omega

def rowCount (n h : ℕ) := 4*h+8+(3*n+2)+(14*n+1)+(3*n*n+n+1)+
  (n*(n*(10*n+4)+2)+4*n+2)+2+(14*n+5)+4

theorem materializeRow_count (buying physical : Vector ℚ n) (budget : ℚ) (allowance : Vector ℚ h)
    (source target : Vector (Fin n) h) (ratio : ℕ) (ratio_ge : 2 ≤ ratio) (raw : Core.RawRow h ratio) :
    (materializeRow input buying physical budget allowance source target ratio raw).events.length ≤ rowCount n h := by
  have depth := Runtime.gridDepth_bound h ratio ratio_ge
  have raw_depth := raw.2.2.isLt
  have empty := emptyState_count input
  have mixed := Weights.mixed_count buying physical (emptyState input).value allowance[raw.1.val] (StoredServe.gridScale budget ratio raw.2.2).value
  have distances := Runtime.ShortestPath.iterate_count
    (ShortestPath.GraphEncoding.ofGraph input.graph (Equiv.refl _))
    (Weights.mixed buying physical (emptyState input).value allowance[raw.1.val] (StoredServe.gridScale budget ratio raw.2.2).value).value
    (Core.rowSource (fun i => source[i.val]) (fun i => target[i.val]) raw.2.1 raw.1) n
  have row := rowFromDistances_count buying ((StoredServe.gridScale budget ratio raw.2.2).value/16)
    (Core.rowMate (fun i => source[i.val]) (fun i => target[i.val]) raw.2.1 raw.1)
    (Runtime.ShortestPath.iterate (ShortestPath.GraphEncoding.ofGraph input.graph (Equiv.refl _))
      (Weights.mixed buying physical (emptyState input).value allowance[raw.1.val] (StoredServe.gridScale budget ratio raw.2.2).value).value
      (Core.rowSource (fun i => source[i.val]) (fun i => target[i.val]) raw.2.1 raw.1) n).value
  simp only [materializeRow, List.length_append, List.length_cons, List.length_nil,
    StoredServe.gridScale_count, Queries.encodingEvents_count, ratDiv_length, ratDiv_value]
  unfold rowCount
  omega

end BuyAtBulk.Computation.Runtime.StoredCore
