import BuyAtBulk.Computation.Core
import BuyAtBulk.UpperBound.ZeroLengthGraph

/-! Complete data-only node rounding. Rational per-request lengths are input
metadata; the routine never enumerates or evaluates fractional path flows. -/
namespace BuyAtBulk.Computation.Rounding
open BuyAtBulk.UpperBound
variable {V : Type} [Fintype V] [DecidableEq V] {n h : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

structure Output (source target : Fin h → V) where
  bought : Finset V
  routes : List (Batch.RouteEntry G source target)

def zeroState (buying : V → ℚ) : RoundingState G :=
  ⟨Core.zeroBuyingNodes numbering buying, [], []⟩

def freeRoutes (physical : V → ℚ) (source target : Fin h → V) (lengths : Fin h → ℚ) (state : RoundingState G) :
    List (Fin h) → Option (List (Batch.RouteEntry G source target))
  | [] => some []
  | i :: order =>
    match Attachment.boughtRoute G numbering physical state (source i) (target i) (lengths i) with
    | none => none
    | some path => (freeRoutes physical source target lengths state order).map (fun entries => ⟨i, path⟩ :: entries)

def raisedOpening (buying opening : V → ℚ) (v : V) : ℚ := if buying v = 0 then 1 else opening v

def zeroTarget (source target : Fin h → V) (lengths : Fin h → ℚ) (i : Fin h) : V :=
  if lengths i = 0 then target i else source i

def zeroGraphDecidableAdj (physical : V → ℚ) : DecidableRel (zeroGraph G physical).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj u v ∧ physical u = 0 ∧ physical v = 0))

def projectZeroEntry (physical : V → ℚ) (source target : Fin h → V) (lengths : Fin h → ℚ)
    (entry : Batch.RouteEntry (zeroGraph G physical) source (zeroTarget source target lengths)) :
    Option (Batch.RouteEntry G source target) :=
  if zero : lengths entry.1 = 0 then
    some ⟨entry.1, ShortestPath.copyPath (projectZeroPath G physical entry.2) rfl (by simp only [zeroTarget, if_pos zero])⟩
  else none

def projectZeroEntries (physical : V → ℚ) (source target : Fin h → V) (lengths : Fin h → ℚ)
    (entries : List (Batch.RouteEntry (zeroGraph G physical) source (zeroTarget source target lengths))) :
    List (Batch.RouteEntry G source target) := entries.filterMap (projectZeroEntry G physical source target lengths)

def zeroActive (lengths : Fin h → ℚ) : Finset (Fin h) := Finset.univ.filter fun i => lengths i = 0
def positiveActive (lengths : Fin h → ℚ) : Finset (Fin h) := Finset.univ.filter fun i => lengths i ≠ 0
def allowance (lengths : Fin h → ℚ) (i : Fin h) : ℚ := if lengths i = 0 then 1 else 64 * lengths i

/-- Openings and budget of the graph induced by zero-physical resources.
Openings of retained resources are left unchanged. -/
def restrictedOpening (buying physical opening : V → ℚ) (v : V) : ℚ :=
  if physical v = 0 then opening v else 0

def restrictedBudget (buying physical opening : V → ℚ) : ℚ :=
  ∑ v, buying v * restrictedOpening buying physical opening v

/-- Isolated representation slots are never returned as purchased resources. -/
def restrictZeroState (physical : V → ℚ) (state : RoundingState (zeroGraph G physical)) :
    RoundingState (zeroGraph G physical) :=
  { state with bought := state.bought.filter fun v => physical v = 0 }

def zeroRun (buying physical opening : V → ℚ) (_budget : ℚ) (source target : Fin h → V)
    (lengths : Fin h → ℚ) :
    Option (RoundingState (zeroGraph G physical) ×
      List (Batch.RouteEntry (zeroGraph G physical) source (zeroTarget source target lengths))) :=
  letI := zeroGraphDecidableAdj G physical
  if zeroActive lengths = ∅ then some (⟨∅, [], []⟩, []) else
  let budget := restrictedBudget buying physical opening
  let result := if budget = 0 then
      let state := zeroState (zeroGraph G physical) numbering buying
      (freeRoutes (zeroGraph G physical) numbering (fun _ => 0) source (zeroTarget source target lengths)
        (fun _ => 0) state (CoreRun.requestOrder (zeroActive lengths) (fun _ => 1))).map
          fun entries => (state, entries)
    else
      Core.run (zeroGraph G physical) numbering buying (fun _ => 0) (restrictedOpening buying physical opening) budget
        (fun _ : Fin h => 1) source (zeroTarget source target lengths) (zeroActive lengths) 8 (binaryDepth h) ∅
  result.map fun result => (restrictZeroState G physical result.1, result.2)

/-- Inactive slots are free self-pairs, so they contribute no helper row. -/
def positiveTarget (source target : Fin h → V) (lengths : Fin h → ℚ) (i : Fin h) : V :=
  if lengths i = 0 then source i else target i

def projectPositiveEntry (source target : Fin h → V) (lengths : Fin h → ℚ)
    (entry : Batch.RouteEntry G source (positiveTarget source target lengths)) :
    Option (Batch.RouteEntry G source target) :=
  if positive : lengths entry.1 ≠ 0 then
    some ⟨entry.1, ShortestPath.copyPath entry.2 rfl (by simp only [positiveTarget, if_neg positive])⟩
  else none

def projectPositiveEntries (source target : Fin h → V) (lengths : Fin h → ℚ)
    (entries : List (Batch.RouteEntry G source (positiveTarget source target lengths))) :
    List (Batch.RouteEntry G source target) := entries.filterMap (projectPositiveEntry G source target lengths)

/-- Stop after zero preprocessing if no positive-rental requests remain. -/
def positiveRun (buying physical opening : V → ℚ) (budget : ℚ) (source target : Fin h → V)
    (lengths : Fin h → ℚ) (ratio r : ℕ) (seed : Finset V) :
    Option (RoundingState G × List (Batch.RouteEntry G source target)) :=
  if positiveActive lengths = ∅ then some (⟨seed, [], []⟩, []) else
    (Core.run G numbering buying physical opening budget (allowance lengths) source
      (positiveTarget source target lengths) (positiveActive lengths) ratio r seed).map
        fun result => (result.1, projectPositiveEntries G source target lengths result.2)

def run (buying physical opening : V → ℚ) (budget : ℚ) (source target : Fin h → V)
    (lengths : Fin h → ℚ) (ratio r : ℕ) : Option (Output G source target) :=
  if h = 0 then some ⟨∅, []⟩ else
    if budget = 0 then
      (freeRoutes G numbering physical source target lengths (zeroState G numbering buying) (List.finRange h)).map
        (fun entries => ⟨(zeroState G numbering buying).bought, entries⟩)
    else
      match zeroRun G numbering buying physical opening budget source target lengths with
      | none => none
      | some (zeroAfter, zeroEntries) =>
        match positiveRun G numbering buying physical opening budget source target lengths ratio r zeroAfter.bought with
        | none => none
        | some (after, entries) =>
          some ⟨after.bought, projectZeroEntries G physical source target lengths zeroEntries ++ entries⟩

end BuyAtBulk.Computation.Rounding
