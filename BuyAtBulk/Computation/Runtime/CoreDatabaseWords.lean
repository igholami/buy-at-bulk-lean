import BuyAtBulk.Computation.Runtime.CoreRowWords
import BuyAtBulk.Computation.Runtime.CoreDatabaseCost

namespace BuyAtBulk.Computation.Runtime.StoredCore
open BuyAtBulk.UpperBound
open Rational
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

theorem sum_width {α : Type} (indices : List α) (width : α → ℕ) (B : ℕ)
    (bounded : ∀ i ∈ indices, width i ≤ B) : (indices.map width).sum ≤ indices.length*B := by
  calc
    _ ≤ (indices.map fun _ => B).sum := List.sum_le_sum bounded
    _ = _ := by simp

theorem rowWidth_le (row : Core.RowValues n) (A T : ℕ) (radius : (Code.ofRat row.radius).bits ≤ A)
    (tolls : ∀ v : Fin n, (Code.ofRat row.toll[v.val]).bits ≤ T) : rowWidth row ≤ A+1+n*T := by
  have bound := sum_width (List.finRange n) (fun v => (Code.ofRat row.toll[v.val]).bits) T (fun v _ => tolls v)
  simp only[List.length_finRange] at bound
  unfold rowWidth
  omega

def databaseWordBudget (n h L : ℕ) :=
  StoredServe.logarithmWordBudget h L+rowWordBudget n h L+
    (2*(2*h+2)+1)*(rowScalarBudget h L+1+n*rowTollBudget n h L)+n+3*h+100

theorem materializeRows_words (buying physical : Vector ℚ n) (budget : ℚ) (allowance : Vector ℚ h)
    (source target : Vector (Fin n) h) (ratio : ℕ) (ratio_ge : 2 ≤ ratio)
    (L : ℕ) (constant : 8 ≤ L)
    (buying_width : ∀ v : Fin n, (Code.ofRat buying[v.val]).bits ≤ L)
    (physical_width : ∀ v : Fin n, (Code.ofRat physical[v.val]).bits ≤ L)
    (budget_width : (Code.ofRat budget).bits ≤ L) (allowance_width : ∀ i : Fin h, (Code.ofRat allowance[i.val]).bits ≤ L)
    (ratio_width : ratio.size ≤ L) :
    WordsWithin (databaseWordBudget n h L) (materializeRows input buying physical budget allowance source target ratio ratio_ge).events := by
  let K := databaseWordBudget n h L
  let D := (StoredServe.gridDepth h ratio).value
  let A := rowScalarBudget h L
  let T := rowTollBudget n h L
  let C := A+1+n*T
  have depth_eq := StoredServe.gridDepth_value h ratio ratio_ge
  have Dbound : D ≤ 2*h+1 := by
    dsimp only[D]
    rw[depth_eq]
    exact Runtime.gridDepth_bound h ratio ratio_ge
  have CK : (2*(2*h+2)+1)*C ≤ K := by dsimp[K,databaseWordBudget,C,A,T];omega
  have rowK : rowWordBudget n h L ≤ K := by dsimp[K,databaseWordBudget];omega
  have ni : n ≤ K := by dsimp[K,databaseWordBudget];omega
  have hi : h ≤ K := by dsimp[K,databaseWordBudget];omega
  have di : D+1 ≤ K := by dsimp[K,databaseWordBudget];omega
  have two : 2 ≤ K := by dsimp[K,databaseWordBudget];omega
  let f := fun (i : Fin h) (side : Fin 2) (d : Fin (D+1)) =>
    materializeRow input buying physical budget allowance source target ratio
      (i,decide (side.val=1),⟨d.val,by have := d.isLt; dsimp only[D] at this; omega⟩)
  let depthWidth := fun cells : Vector (Core.RowValues n) (D+1) => ((List.finRange (D+1)).map fun d => rowWidth cells[d.val]).sum
  let sideWidth := fun sides : Vector (Vector (Core.RowValues n) (D+1)) 2 =>
    ((List.finRange 2).map fun side => ((List.finRange (D+1)).map fun d => rowWidth sides[side.val][d.val]).sum).sum
  have row_words (i : Fin h) (s : Fin 2) (d : Fin (D+1)) : WordsWithin K (f i s d).events :=
    (materializeRow_runtime input buying physical budget allowance source target ratio ratio_ge _ L constant
      buying_width physical_width budget_width allowance_width ratio_width).1.mono rowK
  have row_width (i : Fin h) (s : Fin 2) (d : Fin (D+1)) : rowWidth (f i s d).value ≤ C := by
    have actual := (materializeRow_runtime input buying physical budget allowance source target ratio ratio_ge
      (i,decide (s.val=1),⟨d.val,by have := d.isLt; dsimp only[D] at this;omega⟩) L constant
      buying_width physical_width budget_width allowance_width ratio_width).2
    exact rowWidth_le _ A T actual.1 actual.2
  have perDepth (i : Fin h) (side : Fin 2) :
      WordsWithin K (Weights.materialize (f i side) rowWidth).events :=
    Weights.materialize_words _ _ K di (row_words i side) (fun d => (row_width i side d).trans (by nlinarith))
  have depth_width (i : Fin h) (side : Fin 2) :
      depthWidth (Weights.materialize (f i side) rowWidth).value ≤ (D+1)*C := by
    have actual := sum_width (List.finRange (D+1))
      (fun d => rowWidth (Weights.materialize (f i side) rowWidth).value[d.val]) C
      (by intro d member; simpa only[Weights.materialize_get] using row_width i side d)
    simpa only[depthWidth,List.length_finRange] using actual
  have perSide (i : Fin h) :
      WordsWithin K (Weights.materialize (fun side : Fin 2 => Weights.materialize (f i side) rowWidth) depthWidth).events :=
    Weights.materialize_words _ _ K two (perDepth i) (fun side => (depth_width i side).trans (by nlinarith))
  have side_width (i : Fin h) :
      sideWidth (Weights.materialize (fun side : Fin 2 => Weights.materialize (f i side) rowWidth) depthWidth).value ≤ 2*((D+1)*C) := by
    have actual := sum_width (List.finRange 2)
      (fun side => depthWidth (Weights.materialize (fun side : Fin 2 => Weights.materialize (f i side) rowWidth) depthWidth).value[side.val])
      ((D+1)*C) (by intro side member; simpa only[Weights.materialize_get] using depth_width i side)
    simpa only[sideWidth,depthWidth,List.length_finRange] using actual
  have rows := Weights.materialize_words
    (fun i : Fin h => Weights.materialize (fun side : Fin 2 => Weights.materialize (f i side) rowWidth) depthWidth)
    sideWidth K hi perSide (fun i => (side_width i).trans (by nlinarith))
  have depth := (StoredServe.gridDepth_words h ratio).mono (show StoredServe.logarithmWordBudget h ratio.size ≤ K by
    have product := Nat.mul_le_mul_right (2*h+4) (show 2*ratio.size+2*h+10 ≤ 2*L+2*h+10 by omega)
    dsimp[K,databaseWordBudget,StoredServe.logarithmWordBudget] at *
    omega)
  simpa only[materializeRows,wordsWithin_append,f,depthWidth,sideWidth,D,K,Fin.cast] using And.intro depth rows

end BuyAtBulk.Computation.Runtime.StoredCore
