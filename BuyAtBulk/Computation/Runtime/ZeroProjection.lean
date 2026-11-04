import BuyAtBulk.Computation.Runtime.FreeRounding
import BuyAtBulk.Computation.Runtime.PhaseMetadata

namespace BuyAtBulk.Computation.Runtime.StoredRounding
open BuyAtBulk.UpperBound
open Rational
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

abbrev ZeroEntry (physical : Vector ℚ n) (source target : Vector (Fin n) h) (lengths : Vector ℚ h) :=
  Σ i : Fin h, (zeroGraph input.graph (fun v => physical[v.val])).Path source[i.val]
    (Rounding.zeroTarget (fun i => source[i.val]) (fun i => target[i.val]) (fun i => lengths[i.val]) i)

def projectWalk (physical : Vector ℚ n) {s t : Fin n} :
    (zeroGraph input.graph (fun v => physical[v.val])).Walk s t → Traced (input.graph.Walk s t)
  | .nil => ⟨.nil,[⟨.branch,[1]⟩,⟨.read,[s.val.size]⟩]⟩
  | .cons edge tail =>
    let next := projectWalk physical tail
    ⟨.cons edge.1 next.value,[⟨.branch,[1]⟩,⟨.read,[s.val.size]⟩]++next.events++[⟨.cons,[s.val.size]⟩]⟩

@[simp] theorem projectWalk_value (physical : Vector ℚ n) {s t : Fin n}
    (walk : (zeroGraph input.graph (fun v => physical[v.val])).Walk s t) :
    (projectWalk input physical walk).value=walk.mapLe (zeroGraph_le input.graph (fun v => physical[v.val])) := by
  induction walk with
  | nil => rfl
  | cons edge tail ih => simp[projectWalk,ih,SimpleGraph.Walk.mapLe]

def projectPath (physical : Vector ℚ n) {s t : Fin n}
    (path : (zeroGraph input.graph (fun v => physical[v.val])).Path s t) : Traced (input.graph.Path s t) :=
  let mapped := projectWalk input physical path.val
  ⟨⟨mapped.value,by rw[projectWalk_value];exact (projectZeroPath input.graph (fun v => physical[v.val]) path).property⟩,mapped.events⟩

@[simp] theorem projectPath_value (physical : Vector ℚ n) {s t : Fin n}
    (path : (zeroGraph input.graph (fun v => physical[v.val])).Path s t) :
    (projectPath input physical path).value=projectZeroPath input.graph (fun v => physical[v.val]) path := by
  apply Subtype.ext
  exact projectWalk_value input physical path.val


def projectEntry (physical : Vector ℚ n) (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (entry : ZeroEntry input physical source target lengths) : Traced (Option (StoredBatch.Entry input source target)) :=
  let length := readRat lengths entry.1
  let test := zeroTest length.value
  let prefixEvents := length.events++test.events++[⟨Operation.branch,[1]⟩]
  if guard : test.value=true then
    have zero : lengths[entry.1.val]=0 := of_decide_eq_true guard
    let mapped := projectPath input physical entry.2
    let copied := ShortestPath.copyPath mapped.value rfl (by simp only[Rounding.zeroTarget,if_pos zero])
    ⟨some ⟨entry.1,copied⟩,prefixEvents++mapped.events++[⟨.cons,[entry.1.val.size]⟩]⟩
  else ⟨none,prefixEvents⟩

theorem projectEntry_value (physical : Vector ℚ n) (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (entry : ZeroEntry input physical source target lengths) :
    (projectEntry input physical source target lengths entry).value=
      Rounding.projectZeroEntry input.graph (fun v => physical[v.val]) (fun i => source[i.val]) (fun i => target[i.val])
        (fun i => lengths[i.val]) entry := by
  simp only[projectEntry,Rounding.projectZeroEntry]
  by_cases zero : lengths[entry.1.val]=0 <;>simp[zero,zeroTest,readRat,projectPath_value]


def projectEntries (physical : Vector ℚ n) (source target : Vector (Fin n) h) (lengths : Vector ℚ h) :
    List (ZeroEntry input physical source target lengths) → Traced (List (StoredBatch.Entry input source target))
  | [] => emit .cons [1] []
  | entry::rest =>
    let head := projectEntry input physical source target lengths entry
    let tail := projectEntries physical source target lengths rest
    let events := [⟨Operation.scan,[entry.1.val.size]⟩]++head.events++tail.events++[⟨.branch,[1]⟩]
    match head.value with
    | none => ⟨tail.value,events⟩
    | some projected => ⟨projected::tail.value,events++[⟨.cons,[projected.1.val.size]⟩]⟩

theorem projectEntries_value (physical : Vector ℚ n) (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (entries : List (ZeroEntry input physical source target lengths)) :
    (projectEntries input physical source target lengths entries).value=
      Rounding.projectZeroEntries input.graph (fun v => physical[v.val]) (fun i => source[i.val]) (fun i => target[i.val])
        (fun i => lengths[i.val]) entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only[Rounding.projectZeroEntries,←projectEntry_value] at ih
    simp only[projectEntries,Rounding.projectZeroEntries,List.filterMap_cons,←projectEntry_value]
    split <;>simp_all

end BuyAtBulk.Computation.Runtime.StoredRounding
