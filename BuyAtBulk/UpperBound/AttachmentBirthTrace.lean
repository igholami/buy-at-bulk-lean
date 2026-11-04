import BuyAtBulk.UpperBound.BirthTrace

/-! Birth logs are extracted from the concrete attachment program. The mate
test is the source original-pair test, with reversal for its second endpoint. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

def EndpointPair (s t z mate : V) : Prop := (z = s ∧ mate = t) ∨ (z = t ∧ mate = s)

theorem shortMixedRoute_symm (buying physical : V → ℚ) (state : RoundingState G)
    (allowance scale : ℚ) (s t : V) (threshold : ℚ) :
    HasShortMixedRoute G buying physical state allowance scale s t threshold ↔
      HasShortMixedRoute G buying physical state allowance scale t s threshold := by
  have reverse : ∀ {s t}, HasShortMixedRoute G buying physical state allowance scale s t threshold →
      HasShortMixedRoute G buying physical state allowance scale t s threshold := by
    intro s t route
    obtain ⟨path, short⟩ := route
    refine ⟨path.reverse, ?_⟩
    simpa [NodeMetric.walkWeight, SimpleGraph.Path.reverse, SimpleGraph.Walk.support_reverse] using short
  exact ⟨reverse, reverse⟩

def AttachmentBirthMetadata (allowance scale ratio cutoff : ℚ) (fuel : ℕ) (endpoint mate : V)
    (events : List (BirthEvent G)) : Prop :=
  ∀ event ∈ events, event.endpoint = endpoint ∧ event.mate = mate ∧ event.allowance = allowance ∧
    cutoff < event.scale ∧ ∃ depth ≤ fuel, event.scale = scale / ratio ^ depth

namespace AttachmentExec

theorem birth_trace {buying physical : V → ℚ} {allowance cutoff ratio threshold : ℚ}
    {s t : V} {fuel : ℕ} {scale : ℚ} {z u : V} {inherited : G.Path z u}
    {before after : RoundingState G} {outcome : AttachmentOutcome G s t z u}
    (execution : AttachmentExec G buying physical allowance cutoff ratio threshold s t fuel scale z u inherited before after outcome) :
    ∀ mate, EndpointPair s t z mate → ∃ events,
      BirthTrace G buying physical before events after ∧ AttachmentBirthMetadata allowance scale ratio cutoff fuel z mate events := by
  induction execution with
  | base inherited state small =>
    intro mate context
    exact ⟨[], BirthTrace.progress (NoBirthProgress.buyPath G state inherited) (BirthTrace.refl _), by simp [AttachmentBirthMetadata]⟩
  | complete inherited state above route shortest short =>
    intro mate context
    exact ⟨[], BirthTrace.progress (NoBirthProgress.buyPath G state route) (BirthTrace.refl _), by simp [AttachmentBirthMetadata]⟩
  | @birth currentFuel currentScale endpoint target inherited state continues separated =>
    intro mate context
    let event : BirthEvent G := ⟨endpoint, mate, allowance, currentScale, state⟩
    have guard : BirthGuard G buying physical event := by
      refine ⟨separated, ?_⟩
      rcases context with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact continues.2
      · intro backwards
        exact continues.2 ((shortMixedRoute_symm buying physical state allowance currentScale _ _ _).mpr backwards)
    have progress := NoBirthProgress.trans G (NoBirthProgress.buyPath G (birthAfter G event) inherited)
      (NoBirthProgress.recordEdge G (buyPath G (birthAfter G event) inherited) inherited currentScale)
    refine ⟨[event], BirthTrace.birth event guard (BirthTrace.progress progress (BirthTrace.refl _)), ?_⟩
    intro candidate member
    have heq : candidate = event := by simpa using member
    subst candidate
    exact ⟨rfl, rfl, rfl, continues.1, 0, Nat.zero_le _, by simp [event]⟩
  | @purchase currentFuel currentScale endpoint oldCenter newCenter inherited near state continues eligible shortest short no_bypass =>
    intro mate context
    have progress := NoBirthProgress.trans G
      (NoBirthProgress.trans G (NoBirthProgress.buyPath G state inherited)
        (NoBirthProgress.buyPath G (buyPath G state inherited) near))
      (NoBirthProgress.recordEdge G (buyPath G (buyPath G state inherited) near)
        (inherited.val.reverse.append near.val).toPath currentScale)
    exact ⟨[], BirthTrace.progress progress (BirthTrace.refl _), by simp [AttachmentBirthMetadata]⟩
  | reuse_arm inherited near bypass state final returned continues eligible shortest short bypass_bought bypass_short recursive ih =>
    intro mate context
    obtain ⟨events, trace, metadata⟩ := ih mate context
    refine ⟨events, trace, ?_⟩
    intro event member
    obtain ⟨endpoint, mate_eq, allowance_eq, above_cutoff, depth, depth_le, scale_eq⟩ := metadata event member
    refine ⟨endpoint, mate_eq, allowance_eq, above_cutoff, depth+1, by omega, ?_⟩
    simpa only [pow_succ', div_div] using scale_eq
  | reuse_completed inherited near bypass state final completed continues eligible shortest short bypass_bought bypass_short recursive ih =>
    intro mate context
    obtain ⟨events, trace, metadata⟩ := ih mate context
    refine ⟨events, trace, ?_⟩
    intro event member
    obtain ⟨endpoint, mate_eq, allowance_eq, above_cutoff, depth, depth_le, scale_eq⟩ := metadata event member
    refine ⟨endpoint, mate_eq, allowance_eq, above_cutoff, depth+1, by omega, ?_⟩
    simpa only [pow_succ', div_div] using scale_eq

end AttachmentExec
end BuyAtBulk.UpperBound
