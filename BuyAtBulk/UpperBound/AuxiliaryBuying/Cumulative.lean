import BuyAtBulk.UpperBound.AuxiliaryBuying.GridOrder
import BuyAtBulk.UpperBound.BirthScaleCounts
import BuyAtBulk.UpperBound.GeometricBuying

noncomputable section
namespace BuyAtBulk.UpperBound
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Exact geometric exchange with the actual final high-scale birth-record
counts, preserving every promotion and repeated endpoint record. -/
theorem cumulative_record_scale_sum {buying physical : V → ℚ}
    {before after : RoundingState G} {events : List (BirthEvent G)}
    (trace : BirthTrace G buying physical before events after) (fresh : before.centers = [])
    (budget : ℚ) (budget_pos : 0 < budget) (ratio : ℕ) (ratio_ge : 2 ≤ ratio) (lastDepth : ℕ)
    (covered : ∀ i : Fin events.length, ∃ depth : ℕ, (events.get i).scale = gridScale budget ratio depth) :
    (∑ d : Fin (lastDepth + 1), gridScale budget ratio d *
      ((after.centers.filter fun record => gridScale budget ratio d ≤ record.birthScale).length : ℚ)) ≤
      ((ratio : ℚ) / ((ratio : ℚ) - 1)) * ∑ i : Fin events.length, (events.get i).scale := by
  classical
  let birthDepth : Fin events.length → ℕ := fun i => Classical.choose (covered i)
  have depthScale : ∀ i, (events.get i).scale = gridScale budget ratio (birthDepth i) :=
    fun i => Classical.choose_spec (covered i)
  have count (d : ℕ) :
      ((after.centers.filter fun record => gridScale budget ratio d ≤ record.birthScale).length : ℚ) =
        ∑ i : Fin events.length, if birthDepth i ≤ d then (1 : ℚ) else 0 := by
    rw [BirthTrace.filtered_record_count trace fresh]
    rw [Fintype.card_subtype]
    simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    have equivalent : gridScale budget ratio d ≤ (events.get i).scale ↔ birthDepth i ≤ d := by
      rw [depthScale i, gridScale_le_iff_depth_le budget budget_pos ratio ratio_ge]
    by_cases hd : birthDepth i ≤ d
    · have hscale := equivalent.mpr hd
      change gridScale budget ratio d ≤ events[i.val].scale at hscale
      simp [hd, hscale]
    · have hscale : ¬ gridScale budget ratio d ≤ (events.get i).scale := fun hs => hd (equivalent.mp hs)
      change ¬ gridScale budget ratio d ≤ events[i.val].scale at hscale
      simp [hd, hscale]
  have hleft : (∑ d : Fin (lastDepth + 1), gridScale budget ratio d *
      ((after.centers.filter fun record => gridScale budget ratio d ≤ record.birthScale).length : ℚ)) =
      ∑ d ∈ Finset.range (lastDepth + 1), gridScale budget ratio d *
        (∑ i : Fin events.length, if birthDepth i ≤ d then (1 : ℚ) else 0) := by
    simp_rw [count]
    exact Fin.sum_univ_eq_sum_range
      (fun d : ℕ => gridScale budget ratio d *
        (∑ i : Fin events.length, if birthDepth i ≤ d then (1 : ℚ) else 0)) (lastDepth + 1)
  have hright : (∑ i : Fin events.length, gridScale budget ratio (birthDepth i)) =
      ∑ i : Fin events.length, (events.get i).scale :=
    Finset.sum_congr rfl (fun i hi => (depthScale i).symm)
  rw [hleft]
  have exchange := cumulative_birth_scale_sum budget budget_pos.le ratio ratio_ge lastDepth birthDepth
  rw [hright] at exchange
  exact exchange

end BuyAtBulk.UpperBound
