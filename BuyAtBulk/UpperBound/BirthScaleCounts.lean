import BuyAtBulk.UpperBound.BirthChronology
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Card

/-! Exact list-position counts of eligible birth records, retaining duplicates
and promotions. These connect auxiliary graph vertex counts to actual births. -/
set_option backward.isDefEq.respectTransparency false

namespace BuyAtBulk.UpperBound

theorem list_position_count {A : Type} (events : List A) (predicate : A → Prop)
    [DecidablePred predicate] :
    Fintype.card {i : Fin events.length // predicate (events.get i)} =
      (events.filter fun event => decide (predicate event)).length := by
  rw [Fintype.card_subtype]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  induction events with
  | nil => simp
  | cons a events ih =>
    change (∑ i : Fin (events.length + 1), if predicate ((a :: events).get i) then (1 : ℕ) else 0) = _
    rw [Fin.sum_univ_succ]
    simp only [List.get_cons_zero, List.get_cons_succ', ih]
    by_cases ha : predicate a <;> simp [ha, Nat.add_comm]

namespace BirthTrace

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem filtered_record_count {buying physical : V → ℚ} {before after : RoundingState G}
    {events : List (BirthEvent G)} (trace : BirthTrace G buying physical before events after)
    (fresh : before.centers = []) (scale : ℚ) :
    (after.centers.filter fun record => scale ≤ record.birthScale).length =
      Fintype.card {i : Fin events.length // scale ≤ (events.get i).scale} := by
  rw [record_list G trace, fresh, List.append_nil]
  rw [list_position_count events (fun event : BirthEvent G => scale ≤ event.scale)]
  simp [List.filter_reverse, List.filter_map, Function.comp_def]

end BirthTrace
end BuyAtBulk.UpperBound
