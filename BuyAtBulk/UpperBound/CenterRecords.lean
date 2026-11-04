import Mathlib.Data.List.Basic
import Mathlib.Algebra.Order.Field.Rat

/-! Definition `def:centers`: physical endpoint records, scale eligibility,
and promotions. Multiple records at the same physical endpoint are retained,
so promotion is counted as another birth rather than another graph vertex. -/
namespace BuyAtBulk.UpperBound

structure CenterRecord (Vertex : Type*) where
  endpoint : Vertex
  birthScale : ℚ

/-- Eligibility depends on the existence of a sufficiently high record, not
on the number of records or on the current bought resource set. -/
def EligibleCenter {Vertex : Type*} (records : List (CenterRecord Vertex))
    (vertex : Vertex) (scale : ℚ) : Prop :=
  ∃ record ∈ records, record.endpoint = vertex ∧ scale ≤ record.birthScale

/-- A promotion creates a higher record at an endpoint which already has a
lower record. Its accounting is exactly that of an ordinary birth. -/
def IsPromotion {Vertex : Type*} (records : List (CenterRecord Vertex))
    (vertex : Vertex) (scale : ℚ) : Prop :=
  (∃ record ∈ records, record.endpoint = vertex) ∧ ¬ EligibleCenter records vertex scale

theorem eligible_of_birth {Vertex : Type*} (records : List (CenterRecord Vertex))
    (vertex : Vertex) (scale : ℚ) :
    EligibleCenter (⟨vertex, scale⟩ :: records) vertex scale := by
  exact ⟨⟨vertex, scale⟩, List.mem_cons_self, rfl, le_rfl⟩

theorem eligibility_persists {Vertex : Type*} (records : List (CenterRecord Vertex))
    (birth : CenterRecord Vertex) (vertex : Vertex) (scale : ℚ)
    (eligible : EligibleCenter records vertex scale) :
    EligibleCenter (birth :: records) vertex scale := by
  obtain ⟨record, member, endpoint, high⟩ := eligible
  exact ⟨record, List.mem_cons_of_mem _ member, endpoint, high⟩

theorem eligibility_downward {Vertex : Type*} (records : List (CenterRecord Vertex))
    (vertex : Vertex) (high low : ℚ) (low_le : low ≤ high)
    (eligible : EligibleCenter records vertex high) :
    EligibleCenter records vertex low := by
  obtain ⟨record, member, endpoint, scale_le⟩ := eligible
  exact ⟨record, member, endpoint, low_le.trans scale_le⟩

theorem promotion_counts_one_birth {Vertex : Type*} (records : List (CenterRecord Vertex))
    (vertex : Vertex) (scale : ℚ) :
    (⟨vertex, scale⟩ :: records).length = records.length + 1 := rfl

end BuyAtBulk.UpperBound
