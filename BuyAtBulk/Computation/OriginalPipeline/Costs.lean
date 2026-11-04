import BuyAtBulk.Computation.NodeReduction
import BuyAtBulk.Model.NodeReduction.NodeLPCosts

/-! Executable original-resource cost and opening table scans. -/
set_option maxHeartbeats 1800000
namespace BuyAtBulk.Computation.OriginalPipeline
open BuyAtBulk.NodeReduction BuyAtBulk.CompactFlow
open scoped BuyAtBulk.Computation.NodeReduction
variable (D : GraphData) [DecidableEq D.Vertex]

def resourceCost (cost : Fin D.resourceCount → ℚ) (v : Vertex D) : ℚ :=
  ∑ a, if resourceVertex D a = v then cost a else 0

/-- Free subdivision vertices have opening one; the sole matching paid
resource, if present, replaces this value by its original opening. -/
def resourceOpening (opening : Fin D.resourceCount → ℚ) (v : Vertex D) : ℚ :=
  1 + ∑ a, if resourceVertex D a = v then opening a - 1 else 0

theorem resourceCost_eq (cost : Fin D.resourceCount → ℚ) (v : Vertex D) :
    resourceCost D cost v = nodeCost D cost v := by
  unfold resourceCost nodeCost
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp_all

@[simp] theorem resourceOpening_resource (opening : Fin D.resourceCount → ℚ) (a : Fin D.resourceCount) :
    resourceOpening D opening (resourceVertex D a) = opening a := by
  simp [resourceOpening, (resourceVertex_injective D).eq_iff]

theorem resourceOpening_free (opening : Fin D.resourceCount → ℚ) (v : Vertex D)
    (free : ∀ a, resourceVertex D a ≠ v) : resourceOpening D opening v = 1 := by
  simp [resourceOpening, free]

theorem resourceOpening_bounds (opening : Fin D.resourceCount → ℚ)
    (bounds : ∀ a, 0 ≤ opening a ∧ opening a ≤ 1) (v : Vertex D) :
    0 ≤ resourceOpening D opening v ∧ resourceOpening D opening v ≤ 1 := by
  by_cases paid : ∃ a, resourceVertex D a = v
  · obtain ⟨a, rfl⟩ := paid
    simpa using bounds a
  · rw [resourceOpening_free D opening v (by simpa using paid)]
    norm_num


end BuyAtBulk.Computation.OriginalPipeline
