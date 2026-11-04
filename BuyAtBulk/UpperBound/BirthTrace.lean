import BuyAtBulk.UpperBound.AttachmentInvariants
import BuyAtBulk.UpperBound.AttachmentExecution

/-! Concrete chronological birth metadata. Every logged birth carries its
actual pre-state; guards are derived from source execution, rather than
assuming toll disjointness, packing, or an auxiliary girth conclusion. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

structure BirthEvent where
  endpoint : V
  mate : V
  allowance : ℚ
  scale : ℚ
  before : RoundingState G

def birthAfter (event : BirthEvent G) : RoundingState G :=
  recordBirth G event.before event.endpoint event.scale

def BirthGuard (buying physical : V → ℚ) (event : BirthEvent G) : Prop :=
  (¬ ∃ center, NearEligibleCenter G buying physical event.before event.allowance event.scale event.endpoint center) ∧
    ¬ HasShortMixedRoute G buying physical event.before event.allowance event.scale event.endpoint event.mate (event.scale / 16)

/-- Ordinary purchases and auxiliary insertions preserve records exactly. -/
def NoBirthProgress (before after : RoundingState G) : Prop :=
  before.bought ⊆ after.bought ∧ after.centers = before.centers ∧ before.edges.Sublist after.edges

namespace NoBirthProgress

theorem refl (state : RoundingState G) : NoBirthProgress G state state :=
  ⟨Finset.Subset.refl _, rfl, List.Sublist.refl _⟩

theorem trans {a b c : RoundingState G} (first : NoBirthProgress G a b) (second : NoBirthProgress G b c) :
    NoBirthProgress G a c :=
  ⟨first.1.trans second.1, second.2.1.trans first.2.1, first.2.2.trans second.2.2⟩

theorem buyPath (state : RoundingState G) {u v : V} (path : G.Path u v) :
    NoBirthProgress G state (UpperBound.buyPath G state path) :=
  ⟨bought_subset_buyPath G state path, rfl, List.Sublist.refl _⟩

theorem recordEdge (state : RoundingState G) {u v : V} (path : G.Path u v) (scale : ℚ) :
    NoBirthProgress G state (UpperBound.recordEdge G state path scale) :=
  ⟨Finset.Subset.refl _, rfl, List.sublist_cons_self _ _⟩

end NoBirthProgress

/-- A trace contains every center-record creation between its endpoint
states; unlogged progress cannot create or delete records. -/
inductive BirthTrace (buying physical : V → ℚ) :
    RoundingState G → List (BirthEvent G) → RoundingState G → Prop where
  | refl (state : RoundingState G) : BirthTrace buying physical state [] state
  | progress {before middle after events}
      (step : NoBirthProgress G before middle)
      (rest : BirthTrace buying physical middle events after) :
      BirthTrace buying physical before events after
  | birth (event : BirthEvent G) (guard : BirthGuard G buying physical event) {events after}
      (rest : BirthTrace buying physical (birthAfter G event) events after) :
      BirthTrace buying physical event.before (event :: events) after

namespace BirthTrace

theorem append {buying physical : V → ℚ} {before middle after : RoundingState G}
    {first second : List (BirthEvent G)} (left : BirthTrace G buying physical before first middle)
    (right : BirthTrace G buying physical middle second after) :
    BirthTrace G buying physical before (first ++ second) after := by
  induction left with
  | refl => exact right
  | progress step rest ih => exact BirthTrace.progress step (ih right)
  | birth event guard rest ih => exact BirthTrace.birth event guard (ih right)

theorem guards {buying physical : V → ℚ} {before after : RoundingState G}
    {events : List (BirthEvent G)} (trace : BirthTrace G buying physical before events after) :
    ∀ event ∈ events, BirthGuard G buying physical event := by
  induction trace with
  | refl => simp
  | progress _ _ ih => exact ih
  | birth event guard rest ih =>
    intro candidate member
    cases List.mem_cons.mp member with
    | inl heq => subst candidate; exact guard
    | inr tail => exact ih candidate tail

theorem record_list {buying physical : V → ℚ} {before after : RoundingState G}
    {events : List (BirthEvent G)} (trace : BirthTrace G buying physical before events after) :
    after.centers = (events.map fun event => (⟨event.endpoint, event.scale⟩ : CenterRecord V)).reverse ++ before.centers := by
  induction trace with
  | refl => simp
  | progress step rest ih => simpa only [step.2.1] using ih
  | birth event guard rest ih =>
    dsimp [birthAfter, UpperBound.recordBirth] at ih
    simpa only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append] using ih

theorem record_count {buying physical : V → ℚ} {before after : RoundingState G}
    {events : List (BirthEvent G)} (trace : BirthTrace G buying physical before events after) :
    after.centers.length = before.centers.length + events.length := by
  induction trace with
  | refl => simp
  | progress step rest ih => simpa only [step.2.1] using ih
  | birth event guard rest ih =>
    dsimp [birthAfter, UpperBound.recordBirth] at ih
    simp only [List.length_cons]
    omega

end BirthTrace
end BuyAtBulk.UpperBound
