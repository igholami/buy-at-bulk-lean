import BuyAtBulk.Computation.Runtime.CoreDatabase

namespace BuyAtBulk.Computation.Runtime.StoredCore
open BuyAtBulk.UpperBound
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

def databaseCount (n h : ℕ) := 10*h+12+h*(2*((2*h+2)*(rowCount n h+2)+3)+3)+1

theorem materializeRows_count (buying physical : Vector ℚ n) (budget : ℚ) (allowance : Vector ℚ h)
    (source target : Vector (Fin n) h) (ratio : ℕ) (ratio_ge : 2 ≤ ratio) :
    (materializeRows input buying physical budget allowance source target ratio ratio_ge).events.length ≤ databaseCount n h := by
  let D := (StoredServe.gridDepth h ratio).value
  have depth := StoredServe.gridDepth_count h ratio
  have depth_bound : D ≤ 2*h+1 := by
    dsimp only[D]
    rw [StoredServe.gridDepth_value h ratio ratio_ge]
    exact Runtime.gridDepth_bound h ratio ratio_ge
  let f := fun (i : Fin h) (side : Fin 2) (d : Fin (D+1)) =>
    materializeRow input buying physical budget allowance source target ratio
      (i, decide (side.val=1), ⟨d.val, by have := d.isLt; have same := StoredServe.gridDepth_value h ratio ratio_ge; dsimp only[D] at this; omega⟩)
  let depthWidth := fun cells : Vector (Core.RowValues n) (D+1) => ((List.finRange (D+1)).map fun d => rowWidth cells[d.val]).sum
  let sideWidth := fun sides : Vector (Vector (Core.RowValues n) (D+1)) 2 =>
    ((List.finRange 2).map fun side => ((List.finRange (D+1)).map fun d => rowWidth sides[side.val][d.val]).sum).sum
  have perDepth (i : Fin h) (side : Fin 2) :
      (Weights.materialize (f i side) rowWidth).events.length ≤ (2*h+2)*(rowCount n h+2)+1 := by
    have actual := Weights.materialize_count (f i side) rowWidth (rowCount n h)
      (fun d => materializeRow_count input buying physical budget allowance source target ratio ratio_ge _)
    have product := Nat.mul_le_mul_right (rowCount n h+2) (show D+1 ≤ 2*h+2 by omega)
    omega
  have perSide (i : Fin h) :
      (Weights.materialize (fun side : Fin 2 => Weights.materialize (f i side) rowWidth) depthWidth).events.length ≤
        2*((2*h+2)*(rowCount n h+2)+3)+1 :=
    Weights.materialize_count _ _ _ (perDepth i)
  have total := Weights.materialize_count
    (fun i : Fin h => Weights.materialize (fun side : Fin 2 => Weights.materialize (f i side) rowWidth) depthWidth)
    sideWidth (2*((2*h+2)*(rowCount n h+2)+3)+1) perSide
  simp only[materializeRows,List.length_append]
  unfold databaseCount
  simpa only[Nat.add_assoc, Nat.reduceAdd, f, depthWidth, sideWidth, D, Fin.cast] using Nat.add_le_add depth total

end BuyAtBulk.Computation.Runtime.StoredCore
