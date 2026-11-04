import BuyAtBulk.Computation.PolynomialLP.Trace.Rounded
import BuyAtBulk.Computation.PolynomialLP.Words.Dyadic
import BuyAtBulk.Computation.PolynomialLP.Words.Cells

/-! Actual dyadic center/shape cell reads, temporary scaling and diagonal
addition all have explicit polynomial word bounds. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP.Trace
open Computation Computation.Runtime Rational
variable {n : ℕ}

def roundingCellWordBudget (n p B : ℕ) := n + 4 * (dyadicWordBudget (4 * B + 8) p + B + 10)

theorem roundCenterCell_words (center : Vector ℚ n) (p : ℕ) (i : Fin n) (B : ℕ)
    (input : (Code.ofRat center[i.val]).bits ≤ B) :
    WordsWithin (roundingCellWordBudget n p B) (roundCenterCell center p i).events := by
  have index : i.val.size ≤ n := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt i.isLt)
  have round := (dyadic_words center[i.val] p B input).mono
    (show _ ≤ roundingCellWordBudget n p B by dsimp only [roundingCellWordBudget, dyadicWordBudget]; omega)
  simp only [roundCenterCell, Traced.bind_events, Traced.bind_value, readRat, emit_value, wordsWithin_append]
  refine ⟨?_, round⟩
  simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, and_true]
  dsimp only [roundingCellWordBudget, dyadicWordBudget]
  constructor <;> omega

theorem roundCenterCell_result_bits (center : Vector ℚ n) (p : ℕ) (i : Fin n) (B : ℕ)
    (input : (Code.ofRat center[i.val]).bits ≤ B) :
    (Code.ofRat (roundCenterCell center p i).value).bits ≤ roundingCellWordBudget n p B := by
  have bit := dyadic_result_bits center[i.val] p B input
  change (Code.ofRat (dyadic center[i.val] p).value).bits ≤ _
  dsimp only [roundingCellWordBudget, dyadicWordBudget] at *
  omega

theorem roundShapeCell_words (shape : Vector (Vector ℚ n) n) (scale diag : ℚ)
    (p : ℕ) (i j : Fin n) (B : ℕ)
    (input : (Code.ofRat shape[i.val][j.val]).bits ≤ B)
    (sb : (Code.ofRat scale).bits ≤ B) (db : (Code.ofRat diag).bits ≤ B) :
    WordsWithin (roundingCellWordBudget n p B) (roundShapeCell shape scale diag p i j).events := by
  have ii : i.val.size ≤ n := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt i.isLt)
  have ji : j.val.size ≤ n := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt j.isLt)
  have ni : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have scaled := ratMul_result_bits scale shape[i.val][j.val]
  have scaledBound : (Code.ofRat (scale * shape[i.val][j.val])).bits ≤ 4 * B + 8 := by omega
  have rounded := dyadic_result_bits (scale * shape[i.val][j.val]) p (4 * B + 8) scaledBound
  have zero : (Code.ofRat 0).bits = 3 := by decide
  have extra : (Code.ofRat (if i = j then diag else 0)).bits ≤ B + 3 := by split_ifs <;> omega
  have productWords := WordsWithin.mono (ratMul_words scale shape[i.val][j.val])
    (show _ ≤ roundingCellWordBudget n p B by dsimp only [roundingCellWordBudget, dyadicWordBudget]; omega)
  have roundWords := (dyadic_words (scale * shape[i.val][j.val]) p (4 * B + 8) scaledBound).mono
    (show _ ≤ roundingCellWordBudget n p B by dsimp only [roundingCellWordBudget, dyadicWordBudget]; omega)
  have addWords := WordsWithin.mono (ratAdd_words (dyadic (scale * shape[i.val][j.val]) p).value (if i = j then diag else 0))
    (show _ ≤ roundingCellWordBudget n p B by dsimp only [roundingCellWordBudget, dyadicWordBudget] at *; omega)
  simp only [roundShapeCell, Traced.bind_events, Traced.bind_value, readRat, emit_value,
    ratMul_value, decide_eq_true_eq, wordsWithin_append]
  refine ⟨?_, ?_, productWords, roundWords, ?_, ?_, addWords⟩
  all_goals
    simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, and_true]
    dsimp only [roundingCellWordBudget, dyadicWordBudget]
    repeat' apply And.intro
    all_goals omega

theorem roundShapeCell_result_bits (shape : Vector (Vector ℚ n) n) (scale diag : ℚ)
    (p : ℕ) (i j : Fin n) (B : ℕ)
    (input : (Code.ofRat shape[i.val][j.val]).bits ≤ B)
    (sb : (Code.ofRat scale).bits ≤ B) (db : (Code.ofRat diag).bits ≤ B) :
    (Code.ofRat (roundShapeCell shape scale diag p i j).value).bits ≤ roundingCellWordBudget n p B := by
  have scaled := ratMul_result_bits scale shape[i.val][j.val]
  have scaledBound : (Code.ofRat (scale * shape[i.val][j.val])).bits ≤ 4 * B + 8 := by omega
  have rounded := dyadic_result_bits (scale * shape[i.val][j.val]) p (4 * B + 8) scaledBound
  have zero : (Code.ofRat 0).bits = 3 := by decide
  have extra : (Code.ofRat (if i = j then diag else 0)).bits ≤ B + 3 := by split_ifs <;> omega
  have addition := ratAdd_result_bits (dyadic (scale * shape[i.val][j.val]) p).value (if i = j then diag else 0)
  simp only [roundShapeCell, Traced.bind_value, readRat, emit_value, ratMul_value, ratAdd_value, decide_eq_true_eq]
  dsimp only [roundingCellWordBudget, dyadicWordBudget] at *
  omega

end BuyAtBulk.PolynomialLP.Trace
