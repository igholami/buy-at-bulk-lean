import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith

/-! Exact truncated-distance increment inequality in the proof of Lemma 4.3.
The negative-increment and threshold-crossing cases are included. -/
namespace BuyAtBulk.Tolls

def toll (buying radius distance : ℚ) : ℚ :=
  max 0 (min buying (radius - distance + buying))

theorem toll_nonneg (buying radius distance : ℚ) : 0 ≤ toll buying radius distance :=
  le_max_left _ _

theorem toll_le_buying (buying radius distance : ℚ) (hb : 0 ≤ buying) :
    toll buying radius distance ≤ buying :=
  max_le hb (min_le_left _ _)

theorem toll_le_radius (buying radius distance : ℚ) (hr : 0 ≤ radius)
    (hd : buying ≤ distance) : toll buying radius distance ≤ radius := by
  apply max_le hr
  exact (min_le_right _ _).trans (by linarith)

theorem truncated_increment (buying physical radius previous next : ℚ)
    (hb : 0 ≤ buying) (hp : 0 ≤ physical)
    (prefix_bound : next ≤ previous + buying + physical) :
    min radius next - min radius previous ≤ toll buying radius next + physical := by
  by_cases hprev : previous ≤ radius
  · by_cases hnext : next ≤ radius
    · have ht : toll buying radius next = buying := by
        unfold toll
        rw [min_eq_left (by linarith), max_eq_right hb]
      rw [min_eq_right hnext, min_eq_right hprev, ht]
      linarith
    · have hn : radius ≤ next := (not_le.mp hnext).le
      have ht : radius - next + buying ≤ toll buying radius next := by
        unfold toll
        rw [min_eq_right (by linarith)]
        exact le_max_right _ _
      rw [min_eq_left hn, min_eq_right hprev]
      linarith
  · have hm : min radius previous = radius := min_eq_left (not_le.mp hprev).le
    rw [hm]
    have hn := min_le_left radius next
    have ht := toll_nonneg buying radius next
    linarith

end BuyAtBulk.Tolls
