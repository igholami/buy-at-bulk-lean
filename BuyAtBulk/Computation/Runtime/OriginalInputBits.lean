import BuyAtBulk.Computation.Runtime.OriginalInputSize
import BuyAtBulk.Computation.Runtime.OriginalSolveTrace

/-! Scalar bounds for the actual cached original buffers. Resource scans
return existing stored prices or zero, so no arithmetic growth is hidden here. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace BuyAtBulk.Computation.Runtime.Original
open Rational BuyAtBulk.Computation.StoredOriginal
variable {n resources requests : ℕ} (tables : Tables n resources requests)

theorem cachedBuffers_price_bits (values : Vector ℚ resources) (L : ℕ)
    (inputs : ∀ a : Fin resources,(Code.ofRat values[a.val]).bits ≤ L)
    (zero : (Code.ofRat (0:ℚ)).bits ≤ L)
    (v : Fin (cachedBuffers tables).value.count) :
    (Code.ofRat (sizedPrices tables (enumeration tables).value
      (listLength (enumeration tables).value).value (listLength_value _) values 0).value[v.val]).bits ≤ L := by
  change (Code.ofRat (Weights.materialize _ _).value[v.val]).bits ≤ L
  rw [Weights.materialize_get]
  dsimp only [sizedPriceCell]
  exact resourceValue_output_bits tables values 0 _ L inputs zero

theorem cachedBuffers_buying_bits (L : ℕ) (constant : 5 ≤ L)
    (inputs : ∀ a : Fin resources,(Code.ofRat tables.buying[a.val]).bits ≤ L)
    (v : Fin (cachedBuffers tables).value.count) :
    (Code.ofRat (cachedBuffers tables).value.buying[v.val]).bits ≤ L := by
  exact cachedBuffers_price_bits tables tables.buying L inputs (by norm_num [Code.bits,Code.ofRat];omega) v

theorem cachedBuffers_physical_bits (L : ℕ) (constant : 5 ≤ L)
    (inputs : ∀ a : Fin resources,(Code.ofRat tables.length[a.val]).bits ≤ L)
    (v : Fin (cachedBuffers tables).value.count) :
    (Code.ofRat (cachedBuffers tables).value.physical[v.val]).bits ≤ L := by
  exact cachedBuffers_price_bits tables tables.length L inputs (by norm_num [Code.bits,Code.ofRat];omega) v

def originalLeafBudget : ℕ := inputSize tables+8

theorem originalLeafBudget_constant : 8 ≤ originalLeafBudget tables := by dsimp [originalLeafBudget];omega

theorem cachedData_buying_bits (v : Fin (cachedBuffers tables).value.count) :
    (Code.ofRat ((cachedBuffers tables).value.data tables).buying[v.val]).bits ≤ originalLeafBudget tables :=
  cachedBuffers_buying_bits tables _ (by have := originalLeafBudget_constant tables;omega)
    (fun a=>(inputSize_buying tables a).trans (by dsimp[originalLeafBudget];omega)) v

theorem cachedData_physical_bits (v : Fin (cachedBuffers tables).value.count) :
    (Code.ofRat ((cachedBuffers tables).value.data tables).physical[v.val]).bits ≤ originalLeafBudget tables :=
  cachedBuffers_physical_bits tables _ (by have := originalLeafBudget_constant tables;omega)
    (fun a=>(inputSize_length tables a).trans (by dsimp[originalLeafBudget];omega)) v

theorem cachedData_demand_bits (i : Fin requests) :
    (Code.ofRat ((cachedBuffers tables).value.data tables).demand[i.val]).bits ≤ originalLeafBudget tables := by
  change (Code.ofRat (cachedBuffers tables).value.demand[i.val]).bits ≤ _
  rw [cachedBuffers_demand]
  exact (inputSize_demand tables i).trans (by dsimp[originalLeafBudget];omega)

end BuyAtBulk.Computation.Runtime.Original
