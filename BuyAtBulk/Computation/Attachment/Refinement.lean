import BuyAtBulk.Computation.Attachment.Algorithm

/-! Correctness of the actual computed state/outcome, by induction over fuel.
All semantic branch guards are derived from proved executable query contracts. -/
namespace BuyAtBulk.Computation.Attachment
open BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

theorem run_refines (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (allowance cutoff ratio threshold : ℚ) (allowance_pos : 0 < allowance) (ratio_pos : 0 < ratio)
    (s t : V) (fuel : ℕ) :
    ∀ (scale : ℚ), 0 ≤ scale → ∀ (z u : V) (inherited : G.Path z u) (state : RoundingState G),
      scale / ratio ^ fuel ≤ cutoff →
      AttachmentExec G buying physical allowance cutoff ratio threshold s t fuel scale z u inherited state
        (run G numbering buying physical allowance cutoff ratio threshold s t fuel scale z u inherited state).1
        (run G numbering buying physical allowance cutoff ratio threshold s t fuel scale z u inherited state).2 := by
  induction fuel with
  | zero =>
    intro scale scale_nonneg z u inherited state terminal
    have small : scale ≤ cutoff := by simpa using terminal
    simpa only [run, purchase_eq] using (AttachmentExec.base inherited state small
      (buying := buying) (physical := physical) (allowance := allowance) (ratio := ratio) (threshold := threshold) (s := s) (t := t) (fuel := 0))
  | succ fuel ih =>
    intro scale scale_nonneg z u inherited state terminal
    by_cases small : scale ≤ cutoff
    · simpa only [run, if_pos small, purchase_eq] using (AttachmentExec.base inherited state small
        (buying := buying) (physical := physical) (allowance := allowance) (ratio := ratio) (threshold := threshold) (s := s) (t := t) (fuel := fuel + 1))
    have above : cutoff < scale := lt_of_not_ge small
    have weight_nonneg := mixedWeight_nonneg G buying physical buying_nonneg physical_nonneg state allowance scale allowance_pos scale_nonneg
    cases completion_eq : shortRoute G numbering (mixedWeight G buying physical state allowance scale) s t (scale / 16) with
    | some route =>
      have facts := shortRoute_some G numbering _ weight_nonneg route completion_eq
      rw [mixedWeight_eq] at facts
      simpa only [run, if_neg small, completion_eq, purchase_eq] using
        (AttachmentExec.complete inherited state above route facts.1 facts.2
          (ratio := ratio) (threshold := threshold) (fuel := fuel + 1))
    | none =>
      have no_completion : ¬ HasShortMixedRoute G buying physical state allowance scale s t (scale / 16) := by
        simpa only [HasShortMixedRoute, mixedWeight_eq] using
          (shortRoute_none_iff G numbering _ weight_nonneg s t (scale / 16)).mp completion_eq
      have continues : AttachmentContinues G buying physical state allowance cutoff scale s t := ⟨above, no_completion⟩
      cases near_eq : nearRecord G numbering (mixedWeight G buying physical state allowance scale) scale z state.centers with
      | none =>
        have separated : ¬ ∃ v, NearEligibleCenter G buying physical state allowance scale z v := by
          simpa only [NearEligibleCenter, mixedWeight_eq] using
            nearRecord_none G numbering _ weight_nonneg scale z state.centers near_eq
        simpa only [run, if_neg small, completion_eq, near_eq, purchase_eq] using
          (AttachmentExec.birth inherited state continues separated
            (ratio := ratio) (threshold := threshold) (fuel := fuel + 1))
      | some result =>
        rcases result with ⟨v, near⟩
        have facts := nearRecord_some G numbering _ weight_nonneg scale z state.centers ⟨v, near⟩ near_eq
        rw [mixedWeight_eq] at facts
        cases bypass_eq : boughtRoute G numbering physical state u v threshold with
        | none =>
          have no_bypass := (boughtRoute_none_iff G numbering physical physical_nonneg state u v threshold).mp bypass_eq
          simpa only [run, if_neg small, completion_eq, near_eq, bypass_eq, purchase_eq] using
            (AttachmentExec.purchase inherited near state continues facts.1 facts.2.1 facts.2.2 no_bypass
              (ratio := ratio) (fuel := fuel + 1))
        | some bypass =>
          obtain ⟨supported, short⟩ := boughtRoute_some G numbering physical physical_nonneg state bypass bypass_eq
          have reverse_supported : bypass.reverse.val.support.toFinset ⊆ state.bought := by
            simpa only [SimpleGraph.Path.reverse, SimpleGraph.Walk.support_reverse, List.toFinset_reverse] using supported
          have reverse_short : NodeMetric.walkWeight G physical bypass.reverse.val ≤ threshold := by
            simpa only [NodeMetric.walkWeight, SimpleGraph.Path.reverse, SimpleGraph.Walk.support_reverse, List.toFinset_reverse] using short
          have terminal' : (scale / ratio) / ratio ^ fuel ≤ cutoff := by
            simpa only [pow_succ', div_div] using terminal
          have recursive := ih (scale / ratio) (div_nonneg scale_nonneg ratio_pos.le) z v near state terminal'
          cases recursive_eq : run G numbering buying physical allowance cutoff ratio threshold s t fuel (scale / ratio) z v near state with
          | mk final outcome =>
            rw [recursive_eq] at recursive
            cases outcome with
            | arm returned =>
              simpa only [run, if_neg small, completion_eq, near_eq, bypass_eq, recursive_eq] using
                (AttachmentExec.reuse_arm inherited near bypass.reverse state final returned continues facts.1 facts.2.1 facts.2.2
                  reverse_supported reverse_short recursive)
            | completed completed =>
              simpa only [run, if_neg small, completion_eq, near_eq, bypass_eq, recursive_eq] using
                (AttachmentExec.reuse_completed inherited near bypass.reverse state final completed continues facts.1 facts.2.1 facts.2.2
                  reverse_supported reverse_short recursive)

end BuyAtBulk.Computation.Attachment
