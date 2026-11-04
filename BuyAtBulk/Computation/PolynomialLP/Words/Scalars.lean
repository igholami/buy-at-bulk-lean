import BuyAtBulk.Computation.PolynomialLP.Words.Materialize
import BuyAtBulk.Computation.PolynomialLP.Words.Cells
import BuyAtBulk.Computation.PolynomialLP.Words.Matrix
import BuyAtBulk.Computation.PolynomialLP.Words.Schedule

/-! All operands of the actual cached central-cut scalar updates have
polynomial word bounds. Dimension and normalized input lengths determine them. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace BuyAtBulk.PolynomialLP.Trace
open Computation Computation.Runtime Rational
variable {n : ℕ}

theorem natural_rational_bits (n : ℕ) : (Code.ofRat (n : ℚ)).bits ≤ n + 3 := by
  have size : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  simp [Code.ofRat, Code.bits] <;> omega

def updateQuadraticBudget (n L : ℕ) := matrixProductBudget n (matrixProductBudget n L + L + 5)
def updateLeafBudget (n L : ℕ) := 64 * (L + matrixProductBudget n L + updateQuadraticBudget n L +
  rootBudget n (updateQuadraticBudget n L) + n + 10)
def updateWordBudget (n L : ℕ) := matrixWordBudget n L + quadraticWordBudget n L +
  rootWordBudget n (updateQuadraticBudget n L) + centerCellWordBudget n (updateLeafBudget n L) +
  shapeCellWordBudget n (updateLeafBudget n L) + updateLeafBudget n L + n + 20

theorem rawCenter_words (state : Ellipsoid n) (direction : Vector ℚ n) (L : ℕ) (constant : 5 ≤ L)
    (centerBits : ∀ i : Fin n, (Code.ofRat state.center[i.val]).bits + 1 ≤ L)
    (shapeBits : ∀ i j : Fin n, (Code.ofRat state.shape[i.val][j.val]).bits + 1 ≤ L)
    (directionBits : ∀ i : Fin n, (Code.ofRat direction[i.val]).bits + 1 ≤ L) :
    WordsWithin (updateWordBudget n L) (rawCenter state direction).events := by
  let B := updateLeafBudget n L
  let K := updateWordBudget n L
  let image := (matrixVector state.shape direction).value
  let q := (quadratic state.shape direction).value
  let root := (normalizationRoot q n).value
  let denominator := ((n : ℚ) + 1) * root
  have imageBits (i : Fin n) : (Code.ofRat image[i.val]).bits ≤ matrixProductBudget n L := by
    dsimp only [image]
    rw [matrixVector_value]
    exact PolynomialLP.matrixVector_bits state.shape direction L constant shapeBits directionBits i
  have qBits : (Code.ofRat q).bits ≤ updateQuadraticBudget n L := by
    dsimp only [q, updateQuadraticBudget]
    rw [quadratic_value]
    exact PolynomialLP.quadratic_bits state.shape direction L constant shapeBits directionBits
  have rootBits : (Code.ofRat root).bits ≤ rootBudget n (updateQuadraticBudget n L) := by
    dsimp only [root]
    rw [normalizationRoot_value]
    exact PolynomialLP.normalizationRoot_bits q n _ qBits
  have dimensionBits := natural_rational_bits n
  have oneBits : (Code.ofRat 1).bits = 4 := by decide
  have successorBits := ratAdd_result_bits (n : ℚ) 1
  have denominatorBits := ratMul_result_bits ((n : ℚ) + 1) root
  have denominatorSmall : (Code.ofRat denominator).bits ≤ B := by
    dsimp only [denominator, B, updateLeafBudget]
    rw [oneBits] at successorBits
    omega
  have centerSmall (i : Fin n) : (Code.ofRat state.center[i.val]).bits ≤ B := by
    have small := centerBits i
    dsimp only [B, updateLeafBudget]
    omega
  have imageSmall (i : Fin n) : (Code.ofRat image[i.val]).bits ≤ B := by
    have small := imageBits i
    dsimp only [B, updateLeafBudget]
    omega
  have imageWords := (matrixVector_words state.shape direction L constant shapeBits directionBits).mono
    (show matrixWordBudget n L ≤ K by dsimp only [K, updateWordBudget]; omega)
  have qWords := (quadratic_words state.shape direction L constant shapeBits directionBits).mono
    (show quadraticWordBudget n L ≤ K by dsimp only [K, updateWordBudget]; omega)
  have rootWords := (normalizationRoot_words q n _ qBits).mono
    (show rootWordBudget n (updateQuadraticBudget n L) ≤ K by dsimp only [K, updateWordBudget]; omega)
  have dimensionWords : WordsWithin K (ratCast n).events := by
    have size : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
    simp only [ratCast, emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq, and_true]
    dsimp only [K, updateWordBudget]
    omega
  have successorWords := WordsWithin.mono (ratAdd_words (n : ℚ) 1)
    (show 2 * ((Code.ofRat (n : ℚ)).bits + (Code.ofRat 1).bits) + 8 ≤ K by
      rw [oneBits]; dsimp only [K, updateWordBudget, updateLeafBudget]; omega)
  have denominatorWords := WordsWithin.mono (ratMul_words ((n : ℚ) + 1) root)
    (show _ ≤ K by rw [oneBits] at successorBits; dsimp only [K, updateWordBudget, updateLeafBudget]; omega)
  have output := Weights.materialize_words (centerCell state.center image denominator)
    (fun q : ℚ => (Code.ofRat q).bits) K (by dsimp only [K, updateWordBudget]; omega)
    (fun i => (centerCell_words state.center image denominator i B (centerSmall i) (imageSmall i) denominatorSmall).mono
      (by dsimp only [K, updateWordBudget, B]; omega))
    (fun i => (centerCell_result_bits state.center image denominator i B (centerSmall i) (imageSmall i) denominatorSmall).trans
      (by dsimp only [K, updateWordBudget, B]; omega))
  have dimensionValue : (ratCast n).value = (n : ℚ) := rfl
  simp only [rawCenter, dimensionValue, ratAdd_value, ratMul_value, List.append_assoc, wordsWithin_append]
  exact ⟨imageWords, qWords, rootWords, dimensionWords, successorWords, denominatorWords, output⟩

theorem shapeRows_words (shape : Vector (Vector ℚ n) n) (image : Vector ℚ n) (alpha beta : ℚ)
    (B : ℕ) (shapeBits : ∀ i j : Fin n, (Code.ofRat shape[i.val][j.val]).bits ≤ B)
    (imageBits : ∀ i : Fin n, (Code.ofRat image[i.val]).bits ≤ B)
    (ab : (Code.ofRat alpha).bits ≤ B) (bb : (Code.ofRat beta).bits ≤ B) :
    WordsWithin (shapeCellWordBudget n B) (shapeRows shape image alpha beta).events := by
  have rows (i : Fin n) : WordsWithin (shapeCellWordBudget n B)
      (Weights.materialize (shapeCell shape image alpha beta i) (fun q : ℚ => (Code.ofRat q).bits)).events := by
    apply Weights.materialize_words
    · dsimp only [shapeCellWordBudget]; omega
    · intro j
      exact shapeCell_words shape image alpha beta i j B (shapeBits i j) (imageBits i) (imageBits j) ab bb
    · intro j
      exact shapeCell_result_bits shape image alpha beta i j B (shapeBits i j) (imageBits i) (imageBits j) ab bb
  have size : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  exact Weights.materialize_words _ (fun _ : Vector ℚ n => n.size) _
    (by dsimp only [shapeCellWordBudget]; omega) rows (fun _ => by dsimp only [shapeCellWordBudget]; omega)

theorem rawShape_words (state : Ellipsoid n) (direction : Vector ℚ n) (L : ℕ) (constant : 5 ≤ L)
    (shapeBits : ∀ i j : Fin n, (Code.ofRat state.shape[i.val][j.val]).bits + 1 ≤ L)
    (directionBits : ∀ i : Fin n, (Code.ofRat direction[i.val]).bits + 1 ≤ L) :
    WordsWithin (updateWordBudget n L) (rawShape state direction).events := by
  let B := updateLeafBudget n L
  let K := updateWordBudget n L
  let image := (matrixVector state.shape direction).value
  let q := (quadratic state.shape direction).value
  let square : ℚ := (n : ℚ) * n
  let predecessor := square - 1
  let alpha := square / predecessor
  let denominator := ((n : ℚ) + 1) * q
  let beta := 2 / denominator
  have imageBits (i : Fin n) : (Code.ofRat image[i.val]).bits ≤ matrixProductBudget n L := by
    dsimp only [image]
    rw [matrixVector_value]
    exact PolynomialLP.matrixVector_bits state.shape direction L constant shapeBits directionBits i
  have qBits : (Code.ofRat q).bits ≤ updateQuadraticBudget n L := by
    dsimp only [q, updateQuadraticBudget]
    rw [quadratic_value]
    exact PolynomialLP.quadratic_bits state.shape direction L constant shapeBits directionBits
  have dimensionBits := natural_rational_bits n
  have oneBits : (Code.ofRat 1).bits = 4 := by decide
  have twoBits : (Code.ofRat 2).bits = 5 := by decide
  have squareBits := ratMul_result_bits (n : ℚ) (n : ℚ)
  have predecessorBits := subtract_result_bits square 1
  have alphaBits := ratDiv_result_bits square predecessor
  have successorBits := ratAdd_result_bits (n : ℚ) 1
  have denominatorBits := ratMul_result_bits ((n : ℚ) + 1) q
  have betaBits := ratDiv_result_bits 2 denominator
  have alphaSmall : (Code.ofRat alpha).bits ≤ B := by
    dsimp only [alpha, predecessor, square] at alphaBits predecessorBits ⊢
    rw [oneBits] at predecessorBits
    dsimp only [B, updateLeafBudget]
    omega
  have betaSmall : (Code.ofRat beta).bits ≤ B := by
    dsimp only [beta, denominator] at betaBits ⊢
    rw [oneBits] at successorBits
    rw [twoBits] at betaBits
    dsimp only [B, updateLeafBudget]
    omega
  have shapeSmall (i j : Fin n) : (Code.ofRat state.shape[i.val][j.val]).bits ≤ B := by
    have small := shapeBits i j
    dsimp only [B, updateLeafBudget]
    omega
  have imageSmall (i : Fin n) : (Code.ofRat image[i.val]).bits ≤ B := by
    have small := imageBits i
    dsimp only [B, updateLeafBudget]
    omega
  have imageWords := (matrixVector_words state.shape direction L constant shapeBits directionBits).mono
    (show matrixWordBudget n L ≤ K by dsimp only [K, updateWordBudget]; omega)
  have qWords := (quadratic_words state.shape direction L constant shapeBits directionBits).mono
    (show quadraticWordBudget n L ≤ K by dsimp only [K, updateWordBudget]; omega)
  have dimensionWords : WordsWithin K (ratCast n).events := by
    have size : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
    simp only [ratCast, emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq, and_true]
    dsimp only [K, updateWordBudget]
    omega
  have squareWords := WordsWithin.mono (ratMul_words (n : ℚ) (n : ℚ))
    (show _ ≤ K by dsimp only [K, updateWordBudget, updateLeafBudget]; omega)
  have predecessorWords := (subtract_words square 1).mono
    (show _ ≤ K by rw [oneBits]; dsimp only [square] at squareBits ⊢; dsimp only [K, updateWordBudget, updateLeafBudget]; omega)
  have alphaWords := WordsWithin.mono (ratDiv_words square predecessor)
    (show _ ≤ K by
      dsimp only [square, predecessor] at predecessorBits ⊢
      rw [oneBits] at predecessorBits
      dsimp only [K, updateWordBudget, updateLeafBudget]
      omega)
  have successorWords := WordsWithin.mono (ratAdd_words (n : ℚ) 1)
    (show _ ≤ K by rw [oneBits]; dsimp only [K, updateWordBudget, updateLeafBudget]; omega)
  have denominatorWords := WordsWithin.mono (ratMul_words ((n : ℚ) + 1) q)
    (show _ ≤ K by rw [oneBits] at successorBits; dsimp only [K, updateWordBudget, updateLeafBudget]; omega)
  have betaWords := WordsWithin.mono (ratDiv_words 2 denominator)
    (show _ ≤ K by
      dsimp only [denominator] at denominatorBits ⊢
      rw [twoBits]
      rw [oneBits] at successorBits
      dsimp only [K, updateWordBudget, updateLeafBudget]
      omega)
  have output := (shapeRows_words state.shape image alpha beta B shapeSmall imageSmall alphaSmall betaSmall).mono
    (show shapeCellWordBudget n B ≤ K by dsimp only [K, updateWordBudget, B]; omega)
  have dimensionValue : (ratCast n).value = (n : ℚ) := rfl
  simp only [rawShape, dimensionValue, ratMul_value, ratAdd_value, ratDiv_value,
    subtract_value, List.append_assoc, wordsWithin_append]
  exact ⟨imageWords, qWords, dimensionWords, squareWords, predecessorWords, alphaWords,
    successorWords, denominatorWords, betaWords, output⟩

theorem rawCenter_output_bits (state : Ellipsoid n) (direction : Vector ℚ n) (L : ℕ) (constant : 5 ≤ L)
    (centerBits : ∀ i : Fin n, (Code.ofRat state.center[i.val]).bits + 1 ≤ L)
    (shapeBits : ∀ i j : Fin n, (Code.ofRat state.shape[i.val][j.val]).bits + 1 ≤ L)
    (directionBits : ∀ i : Fin n, (Code.ofRat direction[i.val]).bits + 1 ≤ L) (i : Fin n) :
    (Code.ofRat (rawCenter state direction).value[i.val]).bits ≤ updateWordBudget n L := by
  have whole := rawCenter_words state direction L constant centerBits shapeBits directionBits
  simp only [rawCenter, wordsWithin_append] at whole
  exact Weights.materialize_output_width _ _ _ whole.2 i

theorem rawShape_output_bits (state : Ellipsoid n) (direction : Vector ℚ n) (L : ℕ) (constant : 5 ≤ L)
    (shapeBits : ∀ i j : Fin n, (Code.ofRat state.shape[i.val][j.val]).bits + 1 ≤ L)
    (directionBits : ∀ i : Fin n, (Code.ofRat direction[i.val]).bits + 1 ≤ L) (i j : Fin n) :
    (Code.ofRat (rawShape state direction).value[i.val][j.val]).bits ≤ updateWordBudget n L := by
  have whole := rawShape_words state direction L constant shapeBits directionBits
  simp only [rawShape, wordsWithin_append] at whole
  have row := Weights.materialize_child_words _ _ _ whole.2 i
  have cell := Weights.materialize_output_width _ _ _ row j
  simpa only [rawShape, shapeRows, Weights.materialize_get] using cell

end BuyAtBulk.PolynomialLP.Trace
