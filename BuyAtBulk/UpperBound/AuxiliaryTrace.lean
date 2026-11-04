import BuyAtBulk.UpperBound.BirthChronology
import BuyAtBulk.UpperBound.BuyingCosts
import BuyAtBulk.UpperBound.EligibleEdges

/-! Chronological auxiliary insertions with actual physical realizations,
pre-purchase states, and the source reason for insertion. Graph simplicity,
girth, and packing are conclusions to prove; none is a field of this log. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

structure AuxiliaryEvent where
  edge : AuxiliaryEdge G
  allowance : ℚ
  before : RoundingState G
  after : RoundingState G
  birthReason : Option (V × RoundingState G)

/-- Source branch guard: either no short bought bypass, or an endpoint has
just been born/promoted at this scale and had no eligible record beforehand.
The old auxiliary edge list is unchanged between that birth test and insertion. -/
def AuxiliaryGuard (physical : V → ℚ) (thresholdFactor : ℚ) (event : AuxiliaryEvent G) : Prop :=
  event.after.edges = event.edge :: event.before.edges ∧ StateExtends event.before event.after ∧
    event.edge.realization.val.support.toFinset ⊆ event.after.bought ∧
    EligibleCenter event.after.centers event.edge.source event.edge.scale ∧
    EligibleCenter event.after.centers event.edge.target event.edge.scale ∧
    match event.birthReason with
    | none => ¬ HasShortBoughtRoute G physical event.before event.edge.source event.edge.target
        (thresholdFactor * event.allowance)
    | some (vertex, prior) =>
        (vertex = event.edge.source ∨ vertex = event.edge.target) ∧ prior.edges = event.before.edges ∧
          EdgesEligible G prior ∧ ¬ EligibleCenter prior.centers vertex event.edge.scale

def BirthEdgesNonloop (events : List (AuxiliaryEvent G)) : Prop :=
  ∀ event ∈ events, event.birthReason.isSome = true → event.edge.source ≠ event.edge.target

def AuxiliaryBounds (buying physical : V → ℚ) (ratio : ℚ) (event : AuxiliaryEvent G) : Prop :=
  0 < event.allowance ∧ 0 < event.edge.scale ∧
    NodeMetric.walkWeight G physical event.edge.realization.val ≤ 3 * event.allowance ∧
      addedBuying G buying event.before event.after ≤ (ratio + 1 / 4) * event.edge.scale

/-- Unlogged progress can buy resources or create center records, but cannot
insert an auxiliary edge. Every actual insertion appears exactly once. -/
def NoAuxiliaryProgress (before after : RoundingState G) : Prop :=
  StateExtends before after ∧ after.edges = before.edges

namespace NoAuxiliaryProgress

theorem refl (state : RoundingState G) : NoAuxiliaryProgress G state state :=
  ⟨StateExtends.refl _, rfl⟩

theorem trans {a b c : RoundingState G} (first : NoAuxiliaryProgress G a b) (second : NoAuxiliaryProgress G b c) :
    NoAuxiliaryProgress G a c := ⟨first.1.trans second.1, second.2.trans first.2⟩

theorem buyPath (state : RoundingState G) {u v : V} (path : G.Path u v) :
    NoAuxiliaryProgress G state (UpperBound.buyPath G state path) :=
  ⟨⟨bought_subset_buyPath G state path, List.Sublist.refl _⟩, rfl⟩

theorem recordBirth (state : RoundingState G) (vertex : V) (scale : ℚ) :
    NoAuxiliaryProgress G state (UpperBound.recordBirth G state vertex scale) :=
  ⟨⟨Finset.Subset.refl _, List.sublist_cons_self _ _⟩, rfl⟩

end NoAuxiliaryProgress

inductive AuxiliaryTrace (physical : V → ℚ) (thresholdFactor : ℚ) :
    RoundingState G → List (AuxiliaryEvent G) → RoundingState G → Prop where
  | refl (state : RoundingState G) : AuxiliaryTrace physical thresholdFactor state [] state
  | progress {before middle after events} (step : NoAuxiliaryProgress G before middle)
      (rest : AuxiliaryTrace physical thresholdFactor middle events after) :
      AuxiliaryTrace physical thresholdFactor before events after
  | insert (event : AuxiliaryEvent G) (guard : AuxiliaryGuard G physical thresholdFactor event) {events after}
      (rest : AuxiliaryTrace physical thresholdFactor event.after events after) :
      AuxiliaryTrace physical thresholdFactor event.before (event :: events) after

namespace AuxiliaryTrace

theorem append {physical : V → ℚ} {thresholdFactor : ℚ} {before middle after : RoundingState G}
    {first second : List (AuxiliaryEvent G)} (left : AuxiliaryTrace G physical thresholdFactor before first middle)
    (right : AuxiliaryTrace G physical thresholdFactor middle second after) :
    AuxiliaryTrace G physical thresholdFactor before (first ++ second) after := by
  induction left with
  | refl => exact right
  | progress step rest ih => exact AuxiliaryTrace.progress step (ih right)
  | insert event guard rest ih => exact AuxiliaryTrace.insert event guard (ih right)

theorem state_extends {physical : V → ℚ} {thresholdFactor : ℚ} {before after : RoundingState G}
    {events : List (AuxiliaryEvent G)} (trace : AuxiliaryTrace G physical thresholdFactor before events after) :
    StateExtends before after := by
  induction trace with
  | refl => exact StateExtends.refl _
  | progress step rest ih => exact step.1.trans ih
  | insert event guard rest ih => exact guard.2.1.trans ih

theorem event_prefix {physical : V → ℚ} {thresholdFactor : ℚ} {before after : RoundingState G}
    {events : List (AuxiliaryEvent G)} (trace : AuxiliaryTrace G physical thresholdFactor before events after) :
    ∀ event ∈ events, StateExtends before event.before := by
  induction trace with
  | refl => simp
  | progress step rest ih => intro event member; exact step.1.trans (ih event member)
  | insert event guard rest ih =>
    intro candidate member
    cases List.mem_cons.mp member with
    | inl heq => subst candidate; exact StateExtends.refl _
    | inr tail => exact guard.2.1.trans (ih candidate tail)

theorem event_suffix {physical : V → ℚ} {thresholdFactor : ℚ} {before after : RoundingState G}
    {events : List (AuxiliaryEvent G)} (trace : AuxiliaryTrace G physical thresholdFactor before events after) :
    ∀ event ∈ events, StateExtends event.after after := by
  induction trace with
  | refl => simp
  | progress step rest ih => exact ih
  | insert event guard rest ih =>
    intro candidate member
    cases List.mem_cons.mp member with
    | inl heq => subst candidate; exact state_extends G rest
    | inr tail => exact ih candidate tail

theorem chronological {physical : V → ℚ} {thresholdFactor : ℚ} {before after : RoundingState G}
    {events : List (AuxiliaryEvent G)} (trace : AuxiliaryTrace G physical thresholdFactor before events after) :
    events.Pairwise (fun earlier later => StateExtends earlier.after later.before) := by
  induction trace with
  | refl => exact List.Pairwise.nil
  | progress step rest ih => exact ih
  | insert event guard rest ih => exact List.Pairwise.cons (fun later member => event_prefix G rest later member) ih

theorem guards {physical : V → ℚ} {thresholdFactor : ℚ} {before after : RoundingState G}
    {events : List (AuxiliaryEvent G)} (trace : AuxiliaryTrace G physical thresholdFactor before events after) :
    ∀ event ∈ events, AuxiliaryGuard G physical thresholdFactor event := by
  induction trace with
  | refl => simp
  | progress step rest ih => exact ih
  | insert event guard rest ih =>
    intro candidate member
    cases List.mem_cons.mp member with
    | inl heq => subst candidate; exact guard
    | inr tail => exact ih candidate tail

theorem edge_list {physical : V → ℚ} {thresholdFactor : ℚ} {before after : RoundingState G}
    {events : List (AuxiliaryEvent G)} (trace : AuxiliaryTrace G physical thresholdFactor before events after) :
    after.edges = (events.map AuxiliaryEvent.edge).reverse ++ before.edges := by
  induction trace with
  | refl => simp
  | progress step rest ih => simpa only [step.2] using ih
  | insert event guard rest ih =>
    rw [guard.1] at ih
    simpa only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append] using ih

end AuxiliaryTrace
end BuyAtBulk.UpperBound
