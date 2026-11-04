import BuyAtBulk.UpperBound.AuxiliaryGraph.Chronology
import BuyAtBulk.UpperBound.AttachmentInvariants
import BuyAtBulk.UpperBound.PathCosts

namespace BuyAtBulk.UpperBound.AuxiliaryGraph
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem realize_adj {physical : V → ℚ} {state : RoundingState G} {allowance scale : ℚ}
    (old : OldBounds physical state allowance) {u v : V}
    (adjacent : (atScale state.edges scale).Adj u v) :
    ∃ path : G.Path u v, path.val.support.toFinset ⊆ state.bought ∧
      NodeMetric.walkWeight G physical path.val ≤ 3 * allowance := by
  obtain ⟨⟨edge, member, sameScale, endpoints⟩, distinct⟩ := adjacent
  obtain ⟨bought, short⟩ := old edge member
  rcases Sym2.eq_iff.mp endpoints with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · subst u
    subst v
    exact ⟨edge.realization, bought, short⟩
  · subst u
    subst v
    refine ⟨edge.realization.reverse, ?_, ?_⟩
    · simpa [SimpleGraph.Path.reverse, SimpleGraph.Walk.support_reverse] using bought
    · simpa [NodeMetric.walkWeight, SimpleGraph.Path.reverse, SimpleGraph.Walk.support_reverse] using short

/-- Substitute actual previously bought physical realizations for a nonempty
auxiliary walk. The resulting bought path costs at most `3L` per auxiliary edge,
including intersections between physical realizations. -/
theorem realize_walk {physical : V → ℚ} (physical_nonneg : ∀ v, 0 ≤ physical v)
    {state : RoundingState G} {allowance scale : ℚ} (old : OldBounds physical state allowance)
    {u v : V} (walk : (atScale state.edges scale).Walk u v) (nonempty : ¬ walk.Nil) :
    ∃ path : G.Path u v, path.val.support.toFinset ⊆ state.bought ∧
      NodeMetric.walkWeight G physical path.val ≤ 3 * allowance * (walk.length : ℚ) := by
  induction walk with
  | nil => exact (nonempty SimpleGraph.Walk.Nil.nil).elim
  | @cons u w v adjacent tail ih =>
    obtain ⟨first, boughtFirst, shortFirst⟩ := realize_adj old adjacent
    cases tail with
    | nil => exact ⟨first, boughtFirst, by simpa using shortFirst⟩
    | cons next rest =>
      obtain ⟨last, boughtLast, shortLast⟩ := ih SimpleGraph.Walk.not_nil_cons
      refine ⟨(first.val.append last.val).toPath,
        append_toPath_bought first last state.bought boughtFirst boughtLast, ?_⟩
      calc
        _ ≤ NodeMetric.walkWeight G physical first.val + NodeMetric.walkWeight G physical last.val :=
          (NodeMetric.toPath_weight_le G physical physical_nonneg _).trans
            (walkWeight_append_le G physical physical_nonneg _ _)
        _ ≤ 3 * allowance + 3 * allowance * ((SimpleGraph.Walk.cons next rest).length : ℚ) :=
          add_le_add shortFirst shortLast
        _ = _ := by simp; ring

end BuyAtBulk.UpperBound.AuxiliaryGraph
