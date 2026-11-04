import BuyAtBulk.Computation.Core.Rows
import BuyAtBulk.UpperBound.RunExecution
import BuyAtBulk.UpperBound.CoreRun.Order

/-! Numerical magnitudes do not govern these schedules: the grid loop and
the explicit row list have polynomial bounds in the request count. -/
namespace BuyAtBulk.Computation.Runtime
open BuyAtBulk.UpperBound

theorem gridDepth_bound (h ratio : ℕ) (ratio_ge : 2 ≤ ratio) :
    gridDepth h ratio ≤ 2 * h + 1 := by
  apply Nat.clog_le_of_le_pow
  have power : 2 * h ≤ ratio ^ (2 * h) :=
    (show 2 * h < 2 ^ (2 * h) from Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left ratio_ge _)
  calc
    2 * ratio * h = ratio * (2 * h) := by ring
    _ ≤ ratio * ratio ^ (2 * h) := Nat.mul_le_mul_left ratio power
    _ = ratio ^ (2 * h + 1) := by rw [pow_succ]; ring

theorem rawRows_length (h ratio : ℕ) :
    (Core.rawRows h ratio).length = 2 * h * (gridDepth h ratio + 1) := by
  change ((List.finRange h) ×ˢ ([false, true] ×ˢ (List.finRange (gridDepth h ratio + 1)))).length = _
  simp only [List.length_product, List.length_finRange, List.length_cons, List.length_nil]
  ring

theorem includedRows_length {n h ratio : ℕ} (database : Core.RowDatabase h ratio n) :
    (Core.includedRows database).length ≤ 2 * h * (gridDepth h ratio + 1) := by
  exact (List.length_filter_le _ _).trans_eq (rawRows_length h ratio)

theorem row_schedule_polynomial {n h ratio : ℕ} (database : Core.RowDatabase h ratio n)
    (ratio_ge : 2 ≤ ratio) :
    (Core.includedRows database).length ≤ 4 * h * (h + 1) := by
  have rows := includedRows_length database
  have grid := gridDepth_bound h ratio ratio_ge
  nlinarith

theorem requestOrder_length {h : ℕ} (active : Finset (Fin h)) (allowance : Fin h → ℚ) :
    (CoreRun.requestOrder active allowance).length ≤ h := by
  have distinct := CoreRun.requestOrder_nodup active allowance
  simpa only [Fintype.card_fin] using distinct.length_le_card

end BuyAtBulk.Computation.Runtime
