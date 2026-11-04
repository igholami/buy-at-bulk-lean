import BuyAtBulk.UpperBound.AuxiliaryGraph.Definitions

namespace BuyAtBulk.UpperBound.AuxiliaryGraph
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Every stored record has its actual physical realization in the bought
state, with length bounded against the current request's allowance. -/
def OldBounds (physical : V → ℚ) (state : RoundingState G) (allowance : ℚ) : Prop :=
  ∀ edge ∈ state.edges, edge.realization.val.support.toFinset ⊆ state.bought ∧
    NodeMetric.walkWeight G physical edge.realization.val ≤ 3 * allowance

/-- Chronological allowance order upgrades each earlier realization's own
length bound to the allowance of the current insertion. -/
theorem trace_old_bounds {physical buying : V → ℚ} {Q ratio : ℚ}
    {before after : RoundingState G} {events : List (AuxiliaryEvent G)}
    (trace : AuxiliaryTrace G physical Q before events after)
    (sorted : events.Pairwise fun earlier later => earlier.allowance ≤ later.allowance)
    (bounds : ∀ event ∈ events, AuxiliaryBounds G buying physical ratio event)
    (initial : ∀ event ∈ events, OldBounds physical before event.allowance) :
    ∀ event ∈ events, OldBounds physical event.before event.allowance := by
  induction trace with
  | refl => simp
  | progress step rest ih =>
    apply ih sorted bounds
    intro event he old hold
    rw [step.2] at hold
    obtain ⟨bought, short⟩ := initial event he old hold
    exact ⟨bought.trans step.1.1, short⟩
  | @insert event guard tailEvents final rest ih =>
    obtain ⟨headle, tailsorted⟩ := List.pairwise_cons.mp sorted
    have tailbounds : ∀ (candidate : AuxiliaryEvent G), candidate ∈ tailEvents → AuxiliaryBounds G buying physical ratio candidate :=
      fun candidate he => bounds candidate (List.mem_cons_of_mem _ he)
    have tailinitial : ∀ (candidate : AuxiliaryEvent G), candidate ∈ tailEvents → OldBounds physical event.after candidate.allowance := by
      intro candidate he old hold
      rw [guard.1] at hold
      cases List.mem_cons.mp hold with
      | inl heq =>
        subst old
        exact ⟨guard.2.2.1, (bounds event List.mem_cons_self).2.2.1.trans
          (by linarith [headle candidate he])⟩
      | inr hold =>
        obtain ⟨bought, short⟩ := initial candidate (List.mem_cons_of_mem _ he) old hold
        exact ⟨bought.trans guard.2.1.1, short⟩
    intro candidate he
    cases List.mem_cons.mp he with
    | inl heq => subst candidate; exact initial event List.mem_cons_self
    | inr he => exact ih tailsorted tailbounds tailinitial candidate he

theorem trace_old_bounds_empty {physical buying : V → ℚ} {Q ratio : ℚ}
    {before after : RoundingState G} {events : List (AuxiliaryEvent G)}
    (trace : AuxiliaryTrace G physical Q before events after) (empty : before.edges = [])
    (sorted : events.Pairwise fun earlier later => earlier.allowance ≤ later.allowance)
    (bounds : ∀ event ∈ events, AuxiliaryBounds G buying physical ratio event) :
    ∀ event ∈ events, OldBounds physical event.before event.allowance := by
  apply trace_old_bounds trace sorted bounds
  intro event he edge hedge
  rw [empty] at hedge
  simp at hedge

end BuyAtBulk.UpperBound.AuxiliaryGraph
