import BuyAtBulk.UpperBound.AuxiliaryGraph.SafeInsertion
import BuyAtBulk.UpperBound.AuxiliaryGraph.InsertionGirth

namespace BuyAtBulk.UpperBound.AuxiliaryGraph
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private theorem trace_invariants {physical : V → ℚ} {Q : ℚ} {r : ℕ}
    (hr : 1 ≤ r) {before after : RoundingState G} {events : List (AuxiliaryEvent G)}
    (trace : AuxiliaryTrace G physical Q before events after)
    (distinct : ∀ event ∈ events, event.edge.source ≠ event.edge.target)
    (safe : ∀ event ∈ events,
      ∀ walk : (atScale event.before.edges event.edge.scale).Walk event.edge.source event.edge.target,
        walk.length + 1 ≤ 2 * r → False)
    (initialGirth : ∀ scale, Girth.HighGirth (atScale before.edges scale) r)
    (initialNodup : ∀ scale, (keysAtScale before.edges scale).Nodup) :
    (∀ scale, Girth.HighGirth (atScale after.edges scale) r) ∧
      ∀ scale, (keysAtScale after.edges scale).Nodup := by
  induction trace with
  | refl => exact ⟨initialGirth, initialNodup⟩
  | progress step rest ih =>
    apply ih distinct safe
    · simpa only [step.2] using initialGirth
    · simpa only [step.2] using initialNodup
  | insert event guard rest ih =>
    apply ih
      (fun candidate he => distinct candidate (List.mem_cons_of_mem _ he))
      (fun candidate he => safe candidate (List.mem_cons_of_mem _ he))
    · rw [guard.1]
      exact highGirth_cons _ event.edge (distinct event List.mem_cons_self)
        initialGirth (safe event List.mem_cons_self)
    · rw [guard.1]
      exact nodup_cons _ event.edge hr (distinct event List.mem_cons_self)
        initialNodup (safe event List.mem_cons_self)

/-- Actual trace counterpart of source `lem:aux-girth`, including the
unordered-record simplicity needed to identify paid insertions with edges.
Every alleged short cycle supplies a prior bought bypass contradicting its
last insertion's guard; birth insertions are excluded by actual eligibility. -/
theorem trace_highGirth_nodup {physical buying : V → ℚ}
    (physical_nonneg : ∀ v, 0 ≤ physical v) {Q ratio : ℚ} {r : ℕ}
    (hr : 1 ≤ r) (hQ : 6 * (r : ℚ) ≤ Q)
    {before after : RoundingState G} {events : List (AuxiliaryEvent G)}
    (trace : AuxiliaryTrace G physical Q before events after) (empty : before.edges = [])
    (sorted : events.Pairwise fun earlier later => earlier.allowance ≤ later.allowance)
    (bounds : ∀ event ∈ events, AuxiliaryBounds G buying physical ratio event)
    (distinct : ∀ event ∈ events, event.edge.source ≠ event.edge.target) :
    (∀ scale, Girth.HighGirth (atScale after.edges scale) r) ∧
      ∀ scale, (keysAtScale after.edges scale).Nodup := by
  have old := trace_old_bounds_empty trace empty sorted bounds
  apply trace_invariants hr trace distinct
    (fun event he => no_short_old_walk physical_nonneg hr hQ event
      (AuxiliaryTrace.guards G trace event he) (bounds event he).1 (distinct event he) (old event he))
  · intro scale
    rw [empty, atScale_nil]
    intro v cycle hc
    cases cycle with
    | nil => exact (hc.ne_nil rfl).elim
    | cons adjacent tail => exact adjacent.elim
  · intro scale
    simp [empty, keysAtScale]

end BuyAtBulk.UpperBound.AuxiliaryGraph
