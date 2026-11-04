import BuyAtBulk.Computation.PolynomialLP.Trace.Loop
import BuyAtBulk.Computation.PolynomialLP.Words.Scalars

/-! Binary widths of the actual initial center and diagonal shape arrays. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP.Trace
open Computation Computation.Runtime Rational

def initialWordBudget (n : ℕ) := n + 40

theorem initial_words (n : ℕ) : WordsWithin (initialWordBudget n) (initial n).events := by
  have ni : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have dim := natural_rational_bits n
  have halfBits : (Code.ofRat ((1 : ℚ) / 2)).bits = 5 := by norm_num [Code.ofRat, Code.bits, show Nat.size 2 = 2 by decide]
  have oneBits : (Code.ofRat 1).bits = 4 := by decide
  have twoBits : (Code.ofRat 2).bits = 5 := by decide
  have zeroBits : (Code.ofRat 0).bits = 3 := by decide
  have dimension : WordsWithin (initialWordBudget n) (ratCast n).events := by
    simp only [ratCast, emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq, and_true]
    dsimp only [initialWordBudget]
    omega
  have half := WordsWithin.mono (ratDiv_words 1 2)
    (show _ ≤ initialWordBudget n by rw [oneBits, twoBits]; dsimp only [initialWordBudget]; omega)
  have center := Weights.materialize_words (fun _ : Fin n => Traced.pure ((1 : ℚ) / 2))
    (fun q : ℚ => (Code.ofRat q).bits) (initialWordBudget n)
    (by dsimp only [initialWordBudget]; omega) (by intro i; exact wordsWithin_nil _)
    (by intro i; simp only [Traced.pure_value, halfBits]; dsimp only [initialWordBudget]; omega)
  have rows (i : Fin n) : WordsWithin (initialWordBudget n)
      (Weights.materialize (initialCell (n : ℚ) i) (fun q : ℚ => (Code.ofRat q).bits)).events := by
    apply Weights.materialize_words
    · dsimp only [initialWordBudget]; omega
    · intro j
      have ii : i.val.size ≤ n := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt i.isLt)
      have ji : j.val.size ≤ n := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt j.isLt)
      simp only [initialCell, Traced.bind_events, Traced.bind_value, emit_value, wordsWithin_append,
        emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, forall_eq, and_true]
      dsimp only [initialWordBudget]
      repeat' apply And.intro
      all_goals omega
    · intro j
      rw [initialCell_value]
      dsimp only [initialWordBudget]
      split_ifs <;> omega
  have shape := Weights.materialize_words _ (fun _ : Vector ℚ n => n.size) (initialWordBudget n)
    (by dsimp only [initialWordBudget]; omega) rows (by intro i; dsimp only [initialWordBudget]; omega)
  have dimensionValue : (ratCast n).value = (n : ℚ) := rfl
  simp only [initial, dimensionValue, ratDiv_value, List.append_assoc, wordsWithin_append]
  refine ⟨dimension, half, center, shape, ?_⟩
  simp only [wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq, and_true]
  dsimp only [initialWordBudget]
  omega

end BuyAtBulk.PolynomialLP.Trace
