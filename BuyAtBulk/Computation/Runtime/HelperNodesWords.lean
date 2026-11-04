import BuyAtBulk.Computation.Runtime.HelperNodesRefinement
import BuyAtBulk.Computation.Runtime.HelperTablesWords

namespace BuyAtBulk.Computation.Runtime.MaterializedHelper
open Rational BuyAtBulk.UpperBound
variable {n h ratio m : ℕ}

def nodeWords (n h m L : ℕ) : ℕ :=
  let H := SourceCoefficients.budget n h (L+1)
  tableWords n h m L+24*(m+1)*(n+1)*H+H+n+m+16

theorem nodes_words (buying opening : Vector ℚ n) (budget : ℚ)
    (database : Core.RowDatabase h ratio n) (rows : Vector (Core.RawRow h ratio) m)
    (L : ℕ) (constant : 5≤L) (ratio_ge : 2≤ratio)
    (buyingbits : ∀ v : Fin n, (Code.ofRat buying[v.val]).bits≤L)
    (openingbits : ∀ v : Fin n, (Code.ofRat opening[v.val]).bits≤L)
    (budgetbits : (Code.ofRat budget).bits≤L)
    (radii : ∀ raw : Core.RawRow h ratio, (Code.ofRat (Core.getRow database raw).radius).bits≤L)
    (tolls : ∀ raw : Core.RawRow h ratio, ∀ v : Fin n, (Code.ofRat (Core.getRow database raw).toll[v.val]).bits≤L) :
    WordsWithin (nodeWords n h m L) (nodes buying opening budget database rows).events := by
  let K := nodeWords n h m L
  have table := (tables_words buying opening budget database rows L constant ratio_ge buyingbits openingbits budgetbits
    (fun r => radii rows[r.val]) (fun r => tolls rows[r.val])).mono
    (show tableWords n h m L≤K by dsimp [K,nodeWords];omega)
  have ni : n≤K := by dsimp [K,nodeWords];omega
  have one : 1≤K := by dsimp [K,nodeWords];omega
  have order := indexList_words n K ni
  have heavy := heavyScan_words opening h (List.finRange n) L K constant ni
    (by dsimp [K,nodeWords,tableWords,coefficientCapacity];omega) openingbits
  have coefficients := SourceCoefficients.coefficients_bounded buying opening budget database rows (L+1) (by omega)
    (fun v => Nat.add_le_add_right (buyingbits v) 1) (fun v => Nat.add_le_add_right (openingbits v) 1)
    (Nat.add_le_add_right budgetbits 1) (fun raw => Nat.add_le_add_right (radii raw) 1)
    (fun raw v => Nat.add_le_add_right (tolls raw v) 1)
  have raw := CachedHelper.choose_bounded (SourceCoefficients.tables buying opening budget database rows)
    (SourceCoefficients.budget n h (L+1)) (n+1) coefficients [] (List.finRange n) (by simp)
  have chosen := (RawBridge.trace_words _ _ raw).mono (show _≤K by dsimp [K,nodeWords];omega)
  have joined := appendNodes_words
    (CoefficientPipeline.heavyScan opening h (List.finRange n)).value
    (RawBridge.trace (CachedHelper.choose (SourceCoefficients.tables buying opening budget database rows) [] (List.finRange n))).value
    K ni one
  simpa only [nodes,Traced.bind_events,Traced.bind_value,tables_value,indexList_value,wordsWithin_append] using
    And.intro table (And.intro order (And.intro heavy (And.intro chosen joined)))

end BuyAtBulk.Computation.Runtime.MaterializedHelper
