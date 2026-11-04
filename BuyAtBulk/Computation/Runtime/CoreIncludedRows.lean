import BuyAtBulk.Computation.Runtime.CoreDatabase
import BuyAtBulk.Computation.Runtime.HelperCoefficients

namespace BuyAtBulk.Computation.Runtime.StoredCore
open BuyAtBulk.UpperBound
variable {n h : ℕ}

def rawRows (h ratio : ℕ) (ratio_ge : 2 ≤ ratio) : Traced (List (Core.RawRow h ratio)) :=
  let requests := indexList h
  let D := StoredServe.gridDepth h ratio
  let depths := indexList (D.value+1)
  have depth_eq : D.value+1=UpperBound.gridDepth h ratio+1 := congrArg (·+1) (StoredServe.gridDepth_value h ratio ratio_ge)
  let rows := requests.value.flatMap fun i => ([false,true] : List Bool).flatMap fun side =>
    depths.value.map fun d => (i,side,d.cast depth_eq)
  ⟨rows,requests.events++D.events++depths.events++[⟨.cons,[1]⟩,⟨.cons,[1]⟩]++
    requests.value.flatMap (fun i =>
      [⟨.scan,[i.val.size]⟩]++([false,true] : List Bool).flatMap (fun _ =>
        [⟨.scan,[1]⟩]++depths.value.flatMap (fun d =>
          [⟨.scan,[d.val.size]⟩,⟨.cons,[i.val.size,1,d.val.size]⟩])))⟩

@[simp] theorem map_cast_finRange {α : Type} {d e : ℕ} (same : d=e) (f : Fin e → α) :
    (List.finRange d).map (fun i => f (i.cast same)) = (List.finRange e).map f := by
  subst e
  rfl

theorem rawRows_value (h ratio : ℕ) (ratio_ge : 2 ≤ ratio) : (rawRows h ratio ratio_ge).value=Core.rawRows h ratio := by
  simp only[rawRows,indexList_value,Core.rawRows,List.product,List.map_flatMap,List.map_map]
  apply congrArg (List.flatMap · (List.finRange h))
  funext i
  apply congrArg (List.flatMap · ([false,true] : List Bool))
  funext side
  exact map_cast_finRange _ (fun d => (i,side,d))

/-- Inclusion scans only stored original-mate flags; it never recomputes a
shortest path under the evolving bought set. -/
def filterIncluded {ratio : ℕ} (database : Core.RowDatabase h ratio n) :
    List (Core.RawRow h ratio) → Traced (List (Core.RawRow h ratio))
  | [] => emit .branch [1] []
  | raw::rest =>
    let row := Runtime.getRow database raw
    let next := filterIncluded database rest
    let control := [⟨Operation.scan,[raw.1.val.size,1,raw.2.2.val.size]⟩]++row.events++
      [⟨.read,[1]⟩,⟨.branch,[1]⟩]
    if row.value.included then
      ⟨raw::next.value,control++next.events++[⟨.cons,[raw.1.val.size,1,raw.2.2.val.size]⟩]⟩
    else ⟨next.value,control++next.events⟩

theorem filterIncluded_value {ratio : ℕ} (database : Core.RowDatabase h ratio n) (rows : List (Core.RawRow h ratio)) :
    (filterIncluded database rows).value=rows.filter (fun raw => (Core.getRow database raw).included) := by
  induction rows with
  | nil => rfl
  | cons raw rest ih => simp only[filterIncluded,Runtime.getRow];split_ifs <;>simp_all

def includedRows {ratio : ℕ} (database : Core.RowDatabase h ratio n) (ratio_ge : 2 ≤ ratio) : Traced (List (Core.RawRow h ratio)) := do
  let rows ← rawRows h ratio ratio_ge
  filterIncluded database rows

theorem includedRows_value {ratio : ℕ} (database : Core.RowDatabase h ratio n) (ratio_ge : 2 ≤ ratio) :
    (includedRows database ratio_ge).value=Core.includedRows database := by
  simp [includedRows,rawRows_value,filterIncluded_value,Core.includedRows]

end BuyAtBulk.Computation.Runtime.StoredCore
