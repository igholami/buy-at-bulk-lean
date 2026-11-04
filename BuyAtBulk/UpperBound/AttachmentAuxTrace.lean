import BuyAtBulk.UpperBound.AuxiliaryTrace
import BuyAtBulk.UpperBound.CenterBirthNew
import BuyAtBulk.UpperBound.AttachmentEvents
import BuyAtBulk.UpperBound.AuxiliaryBuyingSum

/-! Concrete auxiliary insertion log extracted from an actual attachment
execution, with pre-purchase bypass guards and actual cost/realization bounds. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

def AttachmentAuxMetadata (allowance scale ratio cutoff : ℚ) (fuel : ℕ)
    (events : List (AuxiliaryEvent G)) : Prop :=
  ∀ event ∈ events, event.allowance = allowance ∧ cutoff < event.edge.scale ∧
    ∃ depth ≤ fuel, event.edge.scale = scale / ratio ^ depth

def ArmAuxiliaryAccount (buying : V → ℚ) (ratio cutoff : ℚ) (before after : RoundingState G)
    (events : List (AuxiliaryEvent G)) {s t z u : V} (outcome : AttachmentOutcome G s t z u) : Prop :=
  match outcome with
  | .arm _ => addedBuying G buying before after ≤ (ratio / 8) * cutoff + auxiliaryBuyingSum G buying events
  | .completed _ => True

namespace AttachmentExec

theorem auxiliary_trace {buying physical : V → ℚ} {allowance cutoff ratio thresholdFactor : ℚ}
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (allowance_pos : 0 < allowance) (ratio_ge : 1 ≤ ratio) (cutoff_nonneg : 0 ≤ cutoff)
    {s t : V} {fuel : ℕ} {scale : ℚ} {z u : V} {inherited : G.Path z u}
    {before after : RoundingState G} {outcome : AttachmentOutcome G s t z u}
    (terminal_buying : buying z = 0) (terminal_physical : physical z = 0)
    (execution : AttachmentExec G buying physical allowance cutoff ratio (thresholdFactor * allowance) s t
      fuel scale z u inherited before after outcome) :
    0 < scale → InheritedArm G buying physical before allowance ratio scale inherited → EdgesEligible G before →
      ∃ events, AuxiliaryTrace G physical thresholdFactor before events after ∧
        AttachmentAuxMetadata allowance scale ratio cutoff fuel events ∧
        (∀ event ∈ events, AuxiliaryBounds G buying physical ratio event) ∧ BirthEdgesNonloop G events ∧
        ArmAuxiliaryAccount buying ratio cutoff before after events outcome := by
  have ratio_pos : 0 < ratio := lt_of_lt_of_le (by norm_num) ratio_ge
  have cheap_nonneg : 0 ≤ (ratio / 8) * cutoff := mul_nonneg (by positivity) cutoff_nonneg
  induction execution with
  | base inherited state small =>
    intro scale_pos inherited_bound old_edges
    refine ⟨[], AuxiliaryTrace.progress (NoAuxiliaryProgress.buyPath G state inherited) (AuxiliaryTrace.refl _), by simp [AttachmentAuxMetadata], by simp, by simp [BirthEdgesNonloop], ?_⟩
    have cost := (buyPath_addedBuying_le_mixed G buying physical physical_nonneg state allowance _ allowance_pos scale_pos.le inherited).trans inherited_bound.2.1
    have cheap := mul_le_mul_of_nonneg_left small (show 0 ≤ ratio / 8 by positivity)
    simpa [ArmAuxiliaryAccount] using cost.trans cheap
  | complete inherited state above route shortest short =>
    intros
    exact ⟨[], AuxiliaryTrace.progress (NoAuxiliaryProgress.buyPath G state route) (AuxiliaryTrace.refl _), by simp [AttachmentAuxMetadata], by simp, by simp [BirthEdgesNonloop], trivial⟩
  | @birth currentFuel currentScale endpoint target inherited state continues separated =>
    intro scale_pos inherited_bound old_edges
    let born := recordBirth G state endpoint currentScale
    let final := recordEdge G (buyPath G born inherited) inherited currentScale
    let event : AuxiliaryEvent G := ⟨⟨endpoint, target, currentScale, inherited⟩, allowance, born, final, some (endpoint, state)⟩
    have guard : AuxiliaryGuard G physical thresholdFactor event := by
      refine ⟨rfl, ⟨bought_subset_buyPath G born inherited, List.Sublist.refl _⟩,
        path_bought_buyPath G born inherited, eligible_of_birth state.centers endpoint currentScale,
        eligibility_persists state.centers ⟨endpoint, currentScale⟩ target currentScale inherited_bound.1, ?_⟩
      exact ⟨Or.inl rfl, rfl, old_edges, separated_center_new G buying physical state allowance currentScale endpoint
        terminal_buying terminal_physical scale_pos.le separated⟩
    have bounds : AuxiliaryBounds G buying physical ratio event := by
      refine ⟨allowance_pos, scale_pos, ?_, ?_⟩
      · dsimp [event]
        linarith [inherited_bound.2.2]
      · exact attachment_birth_buying G buying physical physical_nonneg state allowance ratio currentScale allowance_pos ratio_ge scale_pos.le inherited inherited_bound.2.1
    refine ⟨[event], AuxiliaryTrace.progress (NoAuxiliaryProgress.recordBirth G state endpoint currentScale)
      (AuxiliaryTrace.insert event guard (AuxiliaryTrace.refl _)), ?_, ?_, ?_, ?_⟩
    · intro candidate member
      have heq : candidate = event := by simpa using member
      subst candidate
      exact ⟨rfl, continues.1, 0, Nat.zero_le _, by simp [event]⟩
    · intro candidate member
      have heq : candidate = event := by simpa using member
      simpa only [heq] using bounds
    · intro candidate member _
      have heq : candidate = event := by simpa using member
      subst candidate
      intro same
      change endpoint = target at same
      have old := inherited_bound.1
      have new_record := separated_center_new G buying physical state allowance currentScale endpoint terminal_buying terminal_physical scale_pos.le separated
      apply new_record
      simpa only [same] using old
    · change addedBuying G buying state final ≤ (ratio / 8) * cutoff + auxiliaryBuyingSum G buying [event]
      simp only [auxiliaryBuyingSum_cons, auxiliaryBuyingSum_nil, add_zero]
      change addedBuying G buying state final ≤ (ratio / 8) * cutoff + addedBuying G buying born final
      have same_cost : addedBuying G buying state final = addedBuying G buying born final := rfl
      linarith
  | @purchase currentFuel currentScale endpoint oldCenter newCenter inherited near state continues eligible shortest short no_bypass =>
    intro scale_pos inherited_bound old_edges
    let joined := (inherited.val.reverse.append near.val).toPath
    let final := recordEdge G (buyPath G (buyPath G state inherited) near) joined currentScale
    let event : AuxiliaryEvent G := ⟨⟨oldCenter, newCenter, currentScale, joined⟩, allowance, state, final, none⟩
    have supported_first : inherited.reverse.val.support.toFinset ⊆ final.bought := by
      have support := (path_bought_buyPath G state inherited).trans (bought_subset_buyPath G (buyPath G state inherited) near)
      simpa [final, recordEdge, SimpleGraph.Path.reverse, SimpleGraph.Walk.support_reverse] using support
    have supported_near : near.val.support.toFinset ⊆ final.bought := path_bought_buyPath G (buyPath G state inherited) near
    have guard : AuxiliaryGuard G physical thresholdFactor event := by
      refine ⟨rfl, ⟨(bought_subset_buyPath G state inherited).trans (bought_subset_buyPath G (buyPath G state inherited) near), List.Sublist.refl _⟩,
        append_toPath_bought inherited.reverse near final.bought supported_first supported_near,
        inherited_bound.1, eligible, no_bypass⟩
    have bounds : AuxiliaryBounds G buying physical ratio event := by
      refine ⟨allowance_pos, scale_pos, ?_, ?_⟩
      · exact (attachment_purchase_realization G physical physical_nonneg allowance allowance_pos inherited near inherited_bound.2.2
          (near_arm_physical_bound G buying physical buying_nonneg state allowance currentScale allowance_pos scale_pos near short)).le
      · exact attachment_purchase_buying G buying physical buying_nonneg physical_nonneg state allowance ratio currentScale
          allowance_pos ratio_ge scale_pos.le inherited near inherited_bound.2.1 short
    refine ⟨[event], AuxiliaryTrace.insert event guard (AuxiliaryTrace.refl _), ?_, ?_, ?_, ?_⟩
    · intro candidate member
      have heq : candidate = event := by simpa using member
      subst candidate
      exact ⟨rfl, continues.1, 0, Nat.zero_le _, by simp [event]⟩
    · intro candidate member
      have heq : candidate = event := by simpa using member
      simpa only [heq] using bounds
    · simp [BirthEdgesNonloop, event]
    · change addedBuying G buying state final ≤ (ratio / 8) * cutoff + auxiliaryBuyingSum G buying [event]
      simp only [auxiliaryBuyingSum_cons, auxiliaryBuyingSum_nil, add_zero]
      change addedBuying G buying state final ≤ (ratio / 8) * cutoff + addedBuying G buying state final
      linarith
  | reuse_arm inherited near bypass state final returned continues eligible shortest short bypass_bought bypass_short recursive ih =>
    intro scale_pos _ old_edges
    have near_inherited := near_arm_becomes_inherited G buying physical buying_nonneg physical_nonneg state allowance ratio _ allowance_pos ratio_ge scale_pos near eligible short
    obtain ⟨events, trace, metadata, bounds, nonloops, account⟩ := ih terminal_buying terminal_physical (div_pos scale_pos ratio_pos) near_inherited old_edges
    refine ⟨events, trace, ?_, bounds, nonloops, account⟩
    intro event member
    obtain ⟨allowance_eq, above, depth, depth_le, scale_eq⟩ := metadata event member
    refine ⟨allowance_eq, above, depth+1, by omega, ?_⟩
    simpa only [pow_succ', div_div] using scale_eq
  | reuse_completed inherited near bypass state final completed continues eligible shortest short bypass_bought bypass_short recursive ih =>
    intro scale_pos _ old_edges
    have near_inherited := near_arm_becomes_inherited G buying physical buying_nonneg physical_nonneg state allowance ratio _ allowance_pos ratio_ge scale_pos near eligible short
    obtain ⟨events, trace, metadata, bounds, nonloops, account⟩ := ih terminal_buying terminal_physical (div_pos scale_pos ratio_pos) near_inherited old_edges
    refine ⟨events, trace, ?_, bounds, nonloops, account⟩
    intro event member
    obtain ⟨allowance_eq, above, depth, depth_le, scale_eq⟩ := metadata event member
    refine ⟨allowance_eq, above, depth+1, by omega, ?_⟩
    simpa only [pow_succ', div_div] using scale_eq

end AttachmentExec
end BuyAtBulk.UpperBound
