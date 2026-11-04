import BuyAtBulk.UpperBound.CenterAssignment
import BuyAtBulk.UpperBound.BirthTrace
import BuyAtBulk.UpperBound.AttachmentBirthTrace

/-! Concrete main-assignment birth extraction. The original mate witness is
supplied by selected-scale eligibility before any buying, not by a disjointness
or packing assumption. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

namespace CenterAssignment

theorem birth_trace {buying physical : V → ℚ} {allowance scale : ℚ} {z center : V}
    {before after : RoundingState G} {born : Bool} {arm : G.Path z center}
    (assignment : CenterAssignment G buying physical allowance scale z before after born center arm)
    (mate : V)
    (mate_far : ¬ HasShortMixedRoute G buying physical before allowance scale z mate (scale / 16)) :
    ∃ events, BirthTrace G buying physical before events after ∧
      ∀ event ∈ events, event.endpoint = z ∧ event.mate = mate ∧ event.allowance = allowance ∧ event.scale = scale := by
  induction assignment with
  | existing => exact ⟨[], BirthTrace.refl _, by simp⟩
  | birth separated =>
    let event : BirthEvent G := ⟨z, mate, allowance, scale, before⟩
    refine ⟨[event], BirthTrace.birth event ⟨separated, mate_far⟩ (BirthTrace.refl _), ?_⟩
    intro candidate member
    have heq : candidate = event := by simpa using member
    subst candidate
    exact ⟨rfl, rfl, rfl, rfl⟩

end CenterAssignment

theorem shortMixedRoute_bought_eq (buying physical : V → ℚ) (before after : RoundingState G)
    (bought_eq : after.bought = before.bought) (allowance scale : ℚ) (s t : V) (threshold : ℚ) :
    HasShortMixedRoute G buying physical before allowance scale s t threshold ↔
      HasShortMixedRoute G buying physical after allowance scale s t threshold := by
  have weights : mixedNodeWeight G buying physical before allowance scale =
      mixedNodeWeight G buying physical after allowance scale := by
    funext x
    simp only [mixedNodeWeight, bought_eq]
  exact ⟨fun ⟨path, short⟩ => ⟨path, by simpa only [← weights] using short⟩,
    fun ⟨path, short⟩ => ⟨path, by simpa only [weights] using short⟩⟩

end BuyAtBulk.UpperBound
