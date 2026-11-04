import BuyAtBulk.Computation.PolynomialLP.Trace.Scalars

/-! Fixed-size scalar update arithmetic, including actual normalized
intermediate results and the scalar reads of each materialized cell. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP.Trace
open Computation Computation.Runtime Rational
variable {n : ℕ}

@[simp] theorem negative_bits (q : ℚ) : (Code.ofRat (-q)).bits = (Code.ofRat q).bits := by
  simp [Code.ofRat, Code.bits]

theorem negate_words (q : ℚ) : WordsWithin (Code.ofRat q).bits (negate q).events := by
  simp [negate, emit, WordsWithin]

theorem subtract_result_bits (a b : ℚ) :
    (Code.ofRat (a - b)).bits ≤ 2 * ((Code.ofRat a).bits + (Code.ofRat b).bits) + 8 := by
  simpa only [negative_bits, sub_eq_add_neg] using ratAdd_result_bits a (-b)

theorem subtract_words (a b : ℚ) :
    WordsWithin (2 * ((Code.ofRat a).bits + (Code.ofRat b).bits) + 8) (subtract a b).events := by
  simp only [subtract, Traced.bind_events, Traced.bind_value, negate_value, wordsWithin_append]
  exact ⟨(negate_words b).mono (by omega), by simpa only [negative_bits, WordsWithin] using ratAdd_words a (-b)⟩

def centerCellWordBudget (n B : ℕ) := n + 64 * (B + 2)

theorem centerCell_result_bits (center image : Vector ℚ n) (denominator : ℚ) (i : Fin n)
    (B : ℕ) (cb : (Code.ofRat center[i.val]).bits ≤ B)
    (ub : (Code.ofRat image[i.val]).bits ≤ B) (db : (Code.ofRat denominator).bits ≤ B) :
    (Code.ofRat (centerCell center image denominator i).value).bits ≤ centerCellWordBudget n B := by
  have quotient := ratDiv_result_bits image[i.val] denominator
  have result := subtract_result_bits center[i.val] (image[i.val] / denominator)
  rw [centerCell_value]
  dsimp [centerCellWordBudget]
  omega

theorem centerCell_words (center image : Vector ℚ n) (denominator : ℚ) (i : Fin n)
    (B : ℕ) (cb : (Code.ofRat center[i.val]).bits ≤ B)
    (ub : (Code.ofRat image[i.val]).bits ≤ B) (db : (Code.ofRat denominator).bits ≤ B) :
    WordsWithin (centerCellWordBudget n B) (centerCell center image denominator i).events := by
  have index : i.val.size ≤ n := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt i.isLt)
  have quotient := ratDiv_result_bits image[i.val] denominator
  have division := WordsWithin.mono (ratDiv_words image[i.val] denominator)
    (show _ ≤ centerCellWordBudget n B by dsimp [centerCellWordBudget]; omega)
  have subtraction := (subtract_words center[i.val] (image[i.val] / denominator)).mono
    (show _ ≤ centerCellWordBudget n B by dsimp [centerCellWordBudget]; omega)
  simp only [centerCell, Traced.bind_events, Traced.bind_value, readRat, emit_value,
    ratDiv_value, wordsWithin_append]
  refine ⟨?_, ?_, division, subtraction⟩
  all_goals
    simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, and_true]
    dsimp [centerCellWordBudget]
    constructor <;> omega

def shapeCellWordBudget (n B : ℕ) := n + 256 * (B + 2)

theorem shapeCell_result_bits (shape : Vector (Vector ℚ n) n) (image : Vector ℚ n)
    (alpha beta : ℚ) (i j : Fin n) (B : ℕ)
    (zb : (Code.ofRat shape[i.val][j.val]).bits ≤ B)
    (ub : (Code.ofRat image[i.val]).bits ≤ B) (vb : (Code.ofRat image[j.val]).bits ≤ B)
    (ab : (Code.ofRat alpha).bits ≤ B) (bb : (Code.ofRat beta).bits ≤ B) :
    (Code.ofRat (shapeCell shape image alpha beta i j).value).bits ≤ shapeCellWordBudget n B := by
  have first := ratMul_result_bits beta image[i.val]
  have second := ratMul_result_bits (beta * image[i.val]) image[j.val]
  have residual := subtract_result_bits shape[i.val][j.val] (beta * image[i.val] * image[j.val])
  have output := ratMul_result_bits alpha (shape[i.val][j.val] - beta * image[i.val] * image[j.val])
  rw [shapeCell_value]
  dsimp [shapeCellWordBudget]
  omega

theorem shapeCell_words (shape : Vector (Vector ℚ n) n) (image : Vector ℚ n)
    (alpha beta : ℚ) (i j : Fin n) (B : ℕ)
    (zb : (Code.ofRat shape[i.val][j.val]).bits ≤ B)
    (ub : (Code.ofRat image[i.val]).bits ≤ B) (vb : (Code.ofRat image[j.val]).bits ≤ B)
    (ab : (Code.ofRat alpha).bits ≤ B) (bb : (Code.ofRat beta).bits ≤ B) :
    WordsWithin (shapeCellWordBudget n B) (shapeCell shape image alpha beta i j).events := by
  have ii : i.val.size ≤ n := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt i.isLt)
  have ji : j.val.size ≤ n := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt j.isLt)
  have ni : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have first := ratMul_result_bits beta image[i.val]
  have second := ratMul_result_bits (beta * image[i.val]) image[j.val]
  have residual := subtract_result_bits shape[i.val][j.val] (beta * image[i.val] * image[j.val])
  have firstWords := WordsWithin.mono (ratMul_words beta image[i.val])
    (show _ ≤ shapeCellWordBudget n B by dsimp [shapeCellWordBudget]; omega)
  have secondWords := WordsWithin.mono (ratMul_words (beta * image[i.val]) image[j.val])
    (show _ ≤ shapeCellWordBudget n B by dsimp [shapeCellWordBudget]; omega)
  have residualWords := (subtract_words shape[i.val][j.val] (beta * image[i.val] * image[j.val])).mono
    (show _ ≤ shapeCellWordBudget n B by dsimp [shapeCellWordBudget]; omega)
  have outputWords := WordsWithin.mono
    (ratMul_words alpha (shape[i.val][j.val] - beta * image[i.val] * image[j.val]))
    (show _ ≤ shapeCellWordBudget n B by dsimp [shapeCellWordBudget]; omega)
  simp only [shapeCell, Traced.bind_events, Traced.bind_value, emit_value, readRat,
    ratMul_value, subtract_value, wordsWithin_append]
  refine ⟨?_, ?_, ?_, ?_, firstWords, secondWords, residualWords, outputWords⟩
  all_goals
    simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, and_true]
    dsimp [shapeCellWordBudget]
    constructor <;> omega

end BuyAtBulk.PolynomialLP.Trace
