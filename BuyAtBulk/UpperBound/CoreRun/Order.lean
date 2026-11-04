import Mathlib.Data.List.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.Order.Field.Rat

/-! The source request order is computed by merge sort on rational allowances,
starting from canonical original request indices to fix ties deterministically. -/
namespace BuyAtBulk.UpperBound.CoreRun

/-- Sort exactly the active original requests, preserving their identities. -/
def requestOrder {h : ℕ} (active : Finset (Fin h)) (allowance : Fin h → ℚ) : List (Fin h) :=
  ((List.finRange h).filter fun i => i ∈ active).mergeSort fun i j => decide (allowance i ≤ allowance j)

@[simp] theorem mem_requestOrder {h : ℕ} (active : Finset (Fin h)) (allowance : Fin h → ℚ) (i : Fin h) :
    i ∈ requestOrder active allowance ↔ i ∈ active := by
  unfold requestOrder
  rw [(List.mergeSort_perm _ _).mem_iff]
  simp

theorem requestOrder_nodup {h : ℕ} (active : Finset (Fin h)) (allowance : Fin h → ℚ) :
    (requestOrder active allowance).Nodup := by
  unfold requestOrder
  apply (List.mergeSort_perm _ _).nodup_iff.mpr
  exact (List.nodup_finRange h).filter _

theorem requestOrder_sorted {h : ℕ} (active : Finset (Fin h)) (allowance : Fin h → ℚ) :
    (requestOrder active allowance).Pairwise (fun i j => allowance i ≤ allowance j) := by
  let relation : Fin h → Fin h → Prop := fun i j => allowance i ≤ allowance j
  letI : Std.Total relation := ⟨fun i j => le_total (allowance i) (allowance j)⟩
  letI : IsTrans (Fin h) relation := ⟨fun _ _ _ first second => first.trans second⟩
  exact List.pairwise_mergeSort' relation _

theorem requestOrder_length_le {h : ℕ} (active : Finset (Fin h)) (allowance : Fin h → ℚ) :
    (requestOrder active allowance).length ≤ h := by
  have nodup := requestOrder_nodup active allowance
  have cardinality := Finset.card_le_univ (requestOrder active allowance).toFinset
  rw [List.toFinset_card_of_nodup nodup] at cardinality
  simpa using cardinality

end BuyAtBulk.UpperBound.CoreRun
