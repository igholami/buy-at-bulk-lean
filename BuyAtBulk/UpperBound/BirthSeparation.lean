import BuyAtBulk.UpperBound.BirthChronology
import BuyAtBulk.UpperBound.TollSeparation

/-! Chronological disjointness of actual birth rows on all initially bought
helper nodes. The separation follows from source execution guards and sorted
allowances, not from an assumed packing invariant. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace BirthTrace

theorem toll_rows_pairwise_separated {buying physical : V → ℚ}
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    {before after : RoundingState G} {events : List (BirthEvent G)}
    (trace : BirthTrace G buying physical before events after)
    (allowance_pos : ∀ event ∈ events, 0 < event.allowance)
    (sorted : events.Pairwise fun earlier later => earlier.allowance ≤ later.allowance)
    (helper : Finset V) (helper_bought : helper ⊆ before.bought)
    (scale : ℚ) (scale_pos : 0 < scale) :
    events.Pairwise fun earlier later => earlier.scale = scale → later.scale = scale →
      ∀ v ∈ helper,
        ¬ (0 < Tolls.row G buying physical (scale / earlier.allowance) (scale / 16) earlier.endpoint v ∧
           0 < Tolls.row G buying physical (scale / later.allowance) (scale / 16) later.endpoint v) := by
  apply List.Pairwise.imp_of_mem ?_ (trace.chronological.and sorted)
  intro earlier later he hl pair earlier_scale later_scale v hv
  have eligible := earlier_center_eligible earlier later pair.1 scale (by rw [earlier_scale])
  have guard := (BirthTrace.guards G trace later hl).1
  have no_near : ¬ ∃ u, NearEligibleCenter G buying physical later.before later.allowance scale later.endpoint u := by
    simpa only [later_scale] using guard
  exact Tolls.birth_rows_separated G buying physical buying_nonneg physical_nonneg later.before scale
    earlier.allowance later.allowance scale_pos (allowance_pos earlier he) (allowance_pos later hl)
    pair.2 earlier.endpoint later.endpoint eligible no_near v (trace.helper_retained helper helper_bought later hl hv)

end BirthTrace
end BuyAtBulk.UpperBound
