import BuyAtBulk.UpperBound.GraphDistanceStability
import Mathlib.Tactic.Ring

/-! Downward original-pair eligibility on actual graph distances. Purchases
remain fixed during this comparison; their physical lengths stay present. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

theorem graph_pair_eligibility_downward (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (state : RoundingState G) (allowance small large : ℚ)
    (small_pos : 0 < small) (ordered : small ≤ large) (s t : V)
    (reachable : Nonempty (G.Path s t))
    (eligible : large ≤ NodeMetric.distance G (mixedNodeWeight G buying physical state allowance large) s t reachable) :
    small ≤ NodeMetric.distance G (mixedNodeWeight G buying physical state allowance small) s t reachable := by
  obtain ⟨path, shortest⟩ := NodeMetric.exists_shortest G
    (mixedNodeWeight G buying physical state allowance small) reachable
  have old_le := NodeMetric.distance_le_path G
    (mixedNodeWeight G buying physical state allowance large) reachable path
  have residual_nonneg : 0 ≤ residualWalkBuying G buying state path := by
    unfold residualWalkBuying NodeMetric.walkWeight
    apply Finset.sum_nonneg
    intro v _
    split_ifs
    · exact le_rfl
    · exact buying_nonneg v
  have normalization :
      large * NodeMetric.walkWeight G (mixedNodeWeight G buying physical state allowance small) path.val -
      small * NodeMetric.walkWeight G (mixedNodeWeight G buying physical state allowance large) path.val =
      (large - small) * residualWalkBuying G buying state path := by
    rw [mixedWalk_split, mixedWalk_split]
    ring
  have normalized_nonneg := mul_nonneg (sub_nonneg.mpr ordered) residual_nonneg
  have scaled : large * small ≤ large * NodeMetric.walkWeight G
      (mixedNodeWeight G buying physical state allowance small) path.val := by
    have old_ge := eligible.trans old_le
    have hmul := mul_le_mul_of_nonneg_left old_ge small_pos.le
    linarith
  rw [← shortest]
  exact le_of_mul_le_mul_left scaled (small_pos.trans_le ordered)

end BuyAtBulk.UpperBound
