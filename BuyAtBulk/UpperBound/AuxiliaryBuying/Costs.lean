import BuyAtBulk.UpperBound.AuxiliaryBuying.Cumulative
import BuyAtBulk.UpperBound.AuxiliaryGraph
import BuyAtBulk.UpperBound.BirthScaleSum
import BuyAtBulk.UpperBound.AuxiliaryBuyingSum

noncomputable section
namespace BuyAtBulk.UpperBound
open scoped BigOperators

private theorem list_map_sum_eq_fin {A : Type} (events : List A) (value : A → ℚ) :
    (events.map value).sum = ∑ i : Fin events.length, value (events.get i) := by
  induction events with
  | nil => simp
  | cons a events ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [List.get_cons_zero, List.get_cons_succ']
    exact congrArg (fun total => value a + total) ih

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Sum the actual per-insertion buying bound without discarding repeated
records before the separately proved simplicity theorem is applied. -/
theorem auxiliary_cost_le_scale_sum (buying physical : V → ℚ) (ratio : ℚ)
    (events : List (AuxiliaryEvent G))
    (bounds : ∀ event ∈ events, AuxiliaryBounds G buying physical ratio event) :
    auxiliaryBuyingSum G buying events ≤ (ratio + 1 / 4) *
      ∑ i : Fin events.length, (events.get i).edge.scale := by
  rw [auxiliaryBuyingSum, list_map_sum_eq_fin, Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi => (bounds (events.get i) (List.get_mem ..)).2.2.2

/-- Partition the actual insertion scales over the finite common grid, then
identify each level's log multiplicity with the final stored-record count. -/
theorem auxiliary_scales_le_counts {physical : V → ℚ} {Q : ℚ}
    {before after : RoundingState G} {events : List (AuxiliaryEvent G)}
    (trace : AuxiliaryTrace G physical Q before events after) (fresh : before.edges = [])
    (budget : ℚ) (budget_nonneg : 0 ≤ budget) (ratio lastDepth : ℕ)
    (covered : ∀ i : Fin events.length, ∃ depth : Fin (lastDepth + 1),
      (events.get i).edge.scale = gridScale budget ratio depth) :
    (∑ i : Fin events.length, (events.get i).edge.scale) ≤
      ∑ depth : Fin (lastDepth + 1), gridScale budget ratio depth *
        ((after.edges.filter fun edge => edge.scale = gridScale budget ratio depth).length : ℚ) := by
  classical
  have count (depth : Fin (lastDepth + 1)) :
      Fintype.card {i : Fin events.length // (events.get i).edge.scale = gridScale budget ratio depth} =
        (after.edges.filter fun edge => edge.scale = gridScale budget ratio depth).length := by
    rw [list_position_count events (fun event => event.edge.scale = gridScale budget ratio depth)]
    exact AuxiliaryGraph.event_count_scale trace fresh _
  have hsum := sum_le_level_counts (fun depth : Fin (lastDepth + 1) => gridScale budget ratio depth)
    (fun depth => by unfold gridScale; positivity)
    (fun i : Fin events.length => (events.get i).edge.scale) covered
  simpa only [count] using hsum

end BuyAtBulk.UpperBound
