import BuyAtBulk.UpperBound.AuxiliaryTrace

namespace BuyAtBulk.UpperBound.AuxiliaryGraph
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- All actual auxiliary events are nonloops. Birth edges use their separately
proved fresh-center property. A nonbirth loop would have a bought zero-length
nil route at its free center, contradicting the actual no-bypass branch guard. -/
theorem trace_nonloops {buying physical : V → ℚ} {Q : ℚ}
    {before after : RoundingState G} {events : List (AuxiliaryEvent G)}
    (trace : AuxiliaryTrace G physical Q before events after)
    (births : BirthEdgesNonloop G events)
    (zero_bought : ∀ v, buying v = 0 → v ∈ before.bought)
    (centers_free : ∀ record ∈ after.centers,
      buying record.endpoint = 0 ∧ physical record.endpoint = 0)
    (Q_nonneg : 0 ≤ Q) (allowance_nonneg : ∀ event ∈ events, 0 ≤ event.allowance) :
    ∀ event ∈ events, event.edge.source ≠ event.edge.target := by
  intro event member
  cases reason : event.birthReason with
  | some born => exact births event member (by simp [reason])
  | none =>
    intro loop
    have guard := AuxiliaryTrace.guards G trace event member
    have no_bypass := guard.2.2.2.2.2
    rw [reason] at no_bypass
    obtain ⟨record, hrecord, endpoint, scale⟩ := guard.2.2.2.1
    have suffix := AuxiliaryTrace.event_suffix G trace event member
    have free := centers_free record (suffix.2.subset hrecord)
    have buying_zero : buying event.edge.source = 0 := by simpa only [endpoint] using free.1
    have physical_zero : physical event.edge.source = 0 := by simpa only [endpoint] using free.2
    have statePrefix := AuxiliaryTrace.event_prefix G trace event member
    have bought : event.edge.source ∈ event.before.bought :=
      statePrefix.1 (zero_bought event.edge.source buying_zero)
    apply no_bypass
    rw [← loop]
    refine ⟨⟨.nil, .nil⟩, ?_, ?_⟩
    · intro v hv
      have heq : v = event.edge.source := by simpa using hv
      simpa only [heq] using bought
    · simpa [NodeMetric.walkWeight, physical_zero] using
        mul_nonneg Q_nonneg (allowance_nonneg event member)

end BuyAtBulk.UpperBound.AuxiliaryGraph
