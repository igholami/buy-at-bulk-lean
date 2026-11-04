import BuyAtBulk.UpperBound.BirthTrace

/-! Chronological consequences of the extracted actual birth trace. Earlier
center records remain eligible at later births; initially bought helper nodes
remain bought at every recorded pre-state. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

def StateExtends (before after : RoundingState G) : Prop :=
  before.bought ⊆ after.bought ∧ before.centers.Sublist after.centers

namespace StateExtends

theorem refl (state : RoundingState G) : StateExtends state state :=
  ⟨Finset.Subset.refl _, List.Sublist.refl _⟩

theorem trans {a b c : RoundingState G} (first : StateExtends a b) (second : StateExtends b c) :
    StateExtends a c := ⟨first.1.trans second.1, first.2.trans second.2⟩

theorem birth (event : BirthEvent G) : StateExtends event.before (birthAfter G event) :=
  ⟨Finset.Subset.refl _, List.sublist_cons_self _ _⟩

end StateExtends

namespace BirthTrace

theorem state_extends {buying physical : V → ℚ} {before after : RoundingState G}
    {events : List (BirthEvent G)} (trace : BirthTrace G buying physical before events after) :
    StateExtends before after := by
  induction trace with
  | refl => exact StateExtends.refl _
  | progress step rest ih =>
    refine ⟨step.1.trans ih.1, ?_⟩
    simpa only [step.2.1] using ih.2
  | birth event guard rest ih => exact (StateExtends.birth event).trans ih

theorem event_prefix {buying physical : V → ℚ} {before after : RoundingState G}
    {events : List (BirthEvent G)} (trace : BirthTrace G buying physical before events after) :
    ∀ event ∈ events, StateExtends before event.before := by
  induction trace with
  | refl => simp
  | progress step rest ih =>
    intro event member
    have state_prefix := ih event member
    refine ⟨step.1.trans state_prefix.1, ?_⟩
    simpa only [step.2.1] using state_prefix.2
  | birth event guard rest ih =>
    intro candidate member
    cases List.mem_cons.mp member with
    | inl heq => subst candidate; exact StateExtends.refl _
    | inr tail => exact (StateExtends.birth event).trans (ih candidate tail)

theorem chronological {buying physical : V → ℚ} {before after : RoundingState G}
    {events : List (BirthEvent G)} (trace : BirthTrace G buying physical before events after) :
    events.Pairwise (fun earlier later => StateExtends (birthAfter G earlier) later.before) := by
  induction trace with
  | refl => exact List.Pairwise.nil
  | progress _ _ ih => exact ih
  | birth event guard rest ih => exact List.Pairwise.cons (fun later member => rest.event_prefix later member) ih

theorem helper_retained {buying physical : V → ℚ} {before after : RoundingState G}
    {events : List (BirthEvent G)} (trace : BirthTrace G buying physical before events after)
    (helper : Finset V) (helper_bought : helper ⊆ before.bought) :
    ∀ event ∈ events, helper ⊆ event.before.bought := by
  intro event member
  exact helper_bought.trans (trace.event_prefix event member).1

end BirthTrace

theorem earlier_center_eligible (earlier later : BirthEvent G)
    (chronological : StateExtends (birthAfter G earlier) later.before)
    (scale : ℚ) (scale_le : scale ≤ earlier.scale) :
    EligibleCenter later.before.centers earlier.endpoint scale := by
  exact ⟨⟨earlier.endpoint, earlier.scale⟩, chronological.2.subset List.mem_cons_self, rfl, scale_le⟩

end BuyAtBulk.UpperBound
