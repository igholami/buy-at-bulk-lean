import BuyAtBulk.Computation.PolynomialLP.Words.RoundingScalars
import BuyAtBulk.Computation.PolynomialLP.Words.RoundingCells

/-! Every temporary value of the actual rational rounded central-cut update
has polynomial binary width, before geometric invariants bound the next state. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP.Trace
open Computation Computation.Runtime Rational
variable {n : ℕ}

theorem roundShape_words (shape : Vector (Vector ℚ n) n) (scale diag : ℚ) (p B : ℕ)
    (shapeBits : ∀ i j : Fin n, (Code.ofRat shape[i.val][j.val]).bits ≤ B)
    (sb : (Code.ofRat scale).bits ≤ B) (db : (Code.ofRat diag).bits ≤ B) :
    WordsWithin (roundingCellWordBudget n p B) (roundShape shape scale diag p).events := by
  have rows (i : Fin n) : WordsWithin (roundingCellWordBudget n p B)
      (Weights.materialize (roundShapeCell shape scale diag p i) (fun q : ℚ => (Code.ofRat q).bits)).events := by
    apply Weights.materialize_words
    · dsimp only [roundingCellWordBudget]; omega
    · intro j
      exact roundShapeCell_words shape scale diag p i j B (shapeBits i j) sb db
    · intro j
      exact roundShapeCell_result_bits shape scale diag p i j B (shapeBits i j) sb db
  have size : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  exact Weights.materialize_words _ (fun _ : Vector ℚ n => n.size) _
    (by dsimp only [roundingCellWordBudget]; omega) rows
    (fun _ => by dsimp only [roundingCellWordBudget]; omega)

def roundingLeafBudget (n p L : ℕ) := updateWordBudget n L + inflationWordBudget n + diagonalWordBudget n p + 10

def roundedWordBudget (n p L : ℕ) := updateWordBudget n L + inflationWordBudget n + diagonalWordBudget n p +
  roundingCellWordBudget n p (roundingLeafBudget n p L) + n + 20

theorem roundedStep_words (state : Ellipsoid n) (direction : Vector ℚ n) (p L : ℕ) (constant : 5 ≤ L)
    (centerBits : ∀ i : Fin n, (Code.ofRat state.center[i.val]).bits + 1 ≤ L)
    (shapeBits : ∀ i j : Fin n, (Code.ofRat state.shape[i.val][j.val]).bits + 1 ≤ L)
    (directionBits : ∀ i : Fin n, (Code.ofRat direction[i.val]).bits + 1 ≤ L) :
    WordsWithin (roundedWordBudget n p L) (roundedStep state direction p).events := by
  let B := roundingLeafBudget n p L
  let K := roundedWordBudget n p L
  let center := (rawCenter state direction).value
  let shape := (rawShape state direction).value
  let scale := (inflation n).value
  let diag := (diagonal n p).value
  have centerSmall (i : Fin n) : (Code.ofRat center[i.val]).bits ≤ B :=
    (rawCenter_output_bits state direction L constant centerBits shapeBits directionBits i).trans
      (by dsimp only [B, roundingLeafBudget]; omega)
  have shapeSmall (i j : Fin n) : (Code.ofRat shape[i.val][j.val]).bits ≤ B :=
    (rawShape_output_bits state direction L constant shapeBits directionBits i j).trans
      (by dsimp only [B, roundingLeafBudget]; omega)
  have scaleSmall : (Code.ofRat scale).bits ≤ B := (inflation_result_bits n).trans
    (by dsimp only [B, roundingLeafBudget]; omega)
  have diagSmall : (Code.ofRat diag).bits ≤ B := (diagonal_result_bits n p).trans
    (by dsimp only [B, roundingLeafBudget]; omega)
  have centerWords := (rawCenter_words state direction L constant centerBits shapeBits directionBits).mono
    (show _ ≤ K by dsimp only [K, roundedWordBudget]; omega)
  have shapeWords := (rawShape_words state direction L constant shapeBits directionBits).mono
    (show _ ≤ K by dsimp only [K, roundedWordBudget]; omega)
  have scaleWords := (inflation_words n).mono (show _ ≤ K by dsimp only [K, roundedWordBudget]; omega)
  have diagWords := (diagonal_words n p).mono (show _ ≤ K by dsimp only [K, roundedWordBudget]; omega)
  have roundedCenter := Weights.materialize_words (roundCenterCell center p) (fun q : ℚ => (Code.ofRat q).bits) K
    (by dsimp only [K, roundedWordBudget]; omega)
    (fun i => (roundCenterCell_words center p i B (centerSmall i)).mono
      (by dsimp only [K, roundedWordBudget, B]; omega))
    (fun i => (roundCenterCell_result_bits center p i B (centerSmall i)).trans
      (by dsimp only [K, roundedWordBudget, B]; omega))
  have roundedShape := (roundShape_words shape scale diag p B shapeSmall scaleSmall diagSmall).mono
    (show _ ≤ K by dsimp only [K, roundedWordBudget, B]; omega)
  have size : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  simp only [roundedStep, List.append_assoc, wordsWithin_append]
  refine ⟨centerWords, shapeWords, scaleWords, diagWords, roundedCenter, roundedShape, ?_⟩
  simp only [wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, and_true]
  dsimp only [K, roundedWordBudget]
  constructor <;> omega

end BuyAtBulk.PolynomialLP.Trace
