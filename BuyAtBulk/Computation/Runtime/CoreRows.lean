import BuyAtBulk.Computation.Runtime.BatchWords
import BuyAtBulk.Computation.Core.Rows

/-! Materialized original-metric toll rows. The seed bought set is never read:
every distance table uses the full original buying vector. -/
namespace BuyAtBulk.Computation.Runtime.StoredCore
open BuyAtBulk.UpperBound
open Rational
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

def emptyState : Traced (StoredState.State input.graph) :=
  let flags := Weights.materialize (fun _ : Fin n => emit .write [1] false) (fun _ => 1)
  ⟨⟨flags.value, [], []⟩, flags.events ++ [⟨.cons, [1]⟩]⟩

@[simp] theorem emptyState_bought (v : Fin n) : (emptyState input).value.bought[v.val] = false := by
  simp [emptyState, Weights.materialize]

theorem originalWeight (buying physical : Vector ℚ n) (allowance scale : ℚ) :
    (fun v : Fin n => (Weights.mixed buying physical (emptyState input).value allowance scale).value[v.val]) =
      (fun v : Fin n => buying[v.val]+(scale/allowance)*physical[v.val]) := by
  funext v
  simp [Weights.mixed, Weights.materialize, Weights.mixedCell]

def toll (buying radius distance : ℚ) : Traced ℚ := do
  let negative ← emit .ratNeg [(Code.ofRat distance).bits, (Code.ofRat (-distance)).bits] (-distance)
  let difference ← ratAdd radius negative
  let shifted ← ratAdd difference buying
  let lower ← ratLe buying shifted
  let clipped ← emit .branch [1] (if lower then buying else shifted)
  let positive ← ratLe 0 clipped
  emit .branch [1] (if positive then clipped else 0)

@[simp] theorem toll_value (buying radius distance : ℚ) :
    (toll buying radius distance).value = Tolls.toll buying radius distance := by
  simp only [toll, Traced.bind_value, emit_value, ratAdd_value, ratLe]
  simp only [Tolls.toll, sub_eq_add_neg, min_def, max_def]
  split_ifs <;> simp_all

theorem toll_count (buying radius distance : ℚ) : (toll buying radius distance).events.length = 9 := rfl

def tollFromLabel (buying radius : ℚ) (label : WithTop ℚ) : Traced ℚ :=
  match label with
  | ⊤ => ⟨0, [⟨.branch, [1]⟩, ⟨.write, [(Code.ofRat 0).bits]⟩]⟩
  | (distance : ℚ) =>
      let result := toll buying radius distance
      ⟨result.value, [⟨.branch, [1]⟩] ++ result.events⟩

@[simp] theorem tollFromLabel_value (buying radius : ℚ) (label : WithTop ℚ) :
    (tollFromLabel buying radius label).value = Core.tollFromLabel buying radius label := by
  cases label <;> simp [tollFromLabel, Core.tollFromLabel]

theorem tollFromLabel_count (buying radius : ℚ) (label : WithTop ℚ) :
    (tollFromLabel buying radius label).events.length ≤ 10 := by
  cases label <;> simp [tollFromLabel, toll_count]

def rowFromDistances (buying : Vector ℚ n) (radius : ℚ) (mate : Fin n)
    (distances : Vector (WithTop ℚ) n) : Traced (Core.RowValues n) := do
  let mateLabel ← Runtime.ShortestPath.read distances mate
  let distance ← emit .branch [1, Runtime.ShortestPath.width mateLabel] (mateLabel.untopD 0)
  let included ← ratLess radius distance
  let cells ← Weights.materialize (fun v : Fin n => do
    let buy ← readRat buying v
    let label ← Runtime.ShortestPath.read distances v
    tollFromLabel buy radius label) (fun q : ℚ => (Code.ofRat q).bits)
  emit .cons [(Code.ofRat radius).bits, 1, n.size] ⟨radius, included, cells⟩

@[simp] theorem rowFromDistances_value (buying : Vector ℚ n) (radius : ℚ) (mate : Fin n)
    (distances : Vector (WithTop ℚ) n) :
    (rowFromDistances buying radius mate distances).value = Core.rowFromDistances (fun v => buying[v.val]) radius mate distances := by
  change Core.RowValues.mk _ _ _ = Core.RowValues.mk _ _ _
  congr 1
  apply Vector.ext
  intro i bounded
  simp [rowFromDistances, Weights.materialize, Core.rowFromDistances, readRat, Runtime.ShortestPath.read]

/-- Each row evaluates the source schedule and original metric once, then
stores its actual n toll entries and original-mate inclusion bit. -/
def materializeRow (buying physical : Vector ℚ n) (budget : ℚ) (allowance : Vector ℚ h)
    (source target : Vector (Fin n) h) (ratio : ℕ) (raw : Core.RawRow h ratio) : Traced (Core.RowValues n) :=
  let scale := StoredServe.gridScale budget ratio raw.2.2
  let empty := emptyState input
  let weights := Weights.mixed buying physical empty.value allowance[raw.1.val] scale.value
  let encoded := ShortestPath.GraphEncoding.ofGraph input.graph (Equiv.refl _)
  let origin := Core.rowSource (fun i => source[i.val]) (fun i => target[i.val]) raw.2.1 raw.1
  let mate := Core.rowMate (fun i => source[i.val]) (fun i => target[i.val]) raw.2.1 raw.1
  let distances := Runtime.ShortestPath.iterate encoded weights.value origin n
  let radius := ratDiv scale.value 16
  let row := rowFromDistances buying radius.value mate distances.value
  ⟨row.value, [⟨.index, [raw.1.val.size, 1, raw.2.2.val.size]⟩, ⟨.read, [(Code.ofRat allowance[raw.1.val]).bits]⟩,
      ⟨.branch, [1]⟩, ⟨.read, [origin.val.size, mate.val.size]⟩] ++ scale.events ++ empty.events ++ weights.events ++
      Queries.encodingEvents n ++ distances.events ++ radius.events ++ row.events⟩

theorem materializeRow_value (buying physical : Vector ℚ n) (budget : ℚ) (allowance : Vector ℚ h)
    (source target : Vector (Fin n) h) (ratio : ℕ) (raw : Core.RawRow h ratio) :
    (materializeRow input buying physical budget allowance source target ratio raw).value =
      Core.materializeRow input.graph (Equiv.refl _) (fun v => buying[v.val]) (fun v => physical[v.val]) budget
        (fun i => allowance[i.val]) (fun i => source[i.val]) (fun i => target[i.val]) ratio raw := by
  simp only [materializeRow, rowFromDistances_value, StoredServe.gridScale_value, ratDiv_value,
    Runtime.ShortestPath.iterate_value]
  have weights := originalWeight input buying physical allowance[raw.1.val] (UpperBound.gridScale budget ratio raw.2.2)
  unfold Core.materializeRow ShortestPath.indexedDistances
  simp only [Equiv.refl_apply, Equiv.refl_symm, ShortestPath.shortestDistances]
  congr 1
  congr 1

end BuyAtBulk.Computation.Runtime.StoredCore
