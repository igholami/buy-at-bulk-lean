import BuyAtBulk.Computation.PolynomialLP.Trace.Rounded
import BuyAtBulk.Computation.PolynomialLP.Words.Scalars
import BuyAtBulk.Computation.PolynomialLP.Words.Dyadic

/-! Fixed inflation and diagonal arithmetic include all temporary normalized
rational words and the explicitly generated dyadic denominator. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP.Trace
open Computation Computation.Runtime Rational

def inflationWordBudget (n : ℕ) := 512 * (n + 10)

theorem inflation_words (n : ℕ) : WordsWithin (inflationWordBudget n) (inflation n).events := by
  have db := natural_rational_bits n
  have one : (Code.ofRat 1).bits = 4 := by decide
  have two : (Code.ofRat 2).bits = 5 := by decide
  have sixtyfour : (Code.ofRat 64).bits = 10 := by decide
  have next := ratAdd_result_bits (n : ℚ) 1
  have first := ratMul_result_bits 64 (n : ℚ)
  have denominator := ratMul_result_bits (64 * (n : ℚ)) ((n : ℚ) + 1)
  have eta := ratDiv_result_bits 1 (64 * (n : ℚ) * ((n : ℚ) + 1))
  have doubled := ratMul_result_bits 2 (1 / (64 * (n : ℚ) * ((n : ℚ) + 1)))
  have base := ratAdd_result_bits 1 (2 * (1 / (64 * (n : ℚ) * ((n : ℚ) + 1))))
  rw [one] at next eta base
  rw [two] at doubled
  rw [sixtyfour] at first
  have dimension : WordsWithin (inflationWordBudget n) (ratCast n).events := by
    have size : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
    simp only [ratCast, emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq, and_true]
    dsimp [inflationWordBudget]
    omega
  have add := WordsWithin.mono (ratAdd_words (n : ℚ) 1)
    (show _ ≤ inflationWordBudget n by rw [one]; dsimp [inflationWordBudget]; omega)
  have mul := WordsWithin.mono (ratMul_words 64 (n : ℚ))
    (show _ ≤ inflationWordBudget n by rw [sixtyfour]; dsimp [inflationWordBudget]; omega)
  have den := WordsWithin.mono (ratMul_words (64 * (n : ℚ)) ((n : ℚ) + 1))
    (show _ ≤ inflationWordBudget n by dsimp [inflationWordBudget]; omega)
  have div := WordsWithin.mono (ratDiv_words 1 (64 * (n : ℚ) * ((n : ℚ) + 1)))
    (show _ ≤ inflationWordBudget n by rw [one]; dsimp [inflationWordBudget]; omega)
  have double := WordsWithin.mono (ratMul_words 2 (1 / (64 * (n : ℚ) * ((n : ℚ) + 1))))
    (show _ ≤ inflationWordBudget n by rw [two]; dsimp [inflationWordBudget]; omega)
  have addBase := WordsWithin.mono (ratAdd_words 1 (2 * (1 / (64 * (n : ℚ) * ((n : ℚ) + 1)))))
    (show _ ≤ inflationWordBudget n by rw [one]; dsimp [inflationWordBudget]; omega)
  let value : ℚ := 1 + 2 * (1 / (64 * (n : ℚ) * ((n : ℚ) + 1)))
  have square := WordsWithin.mono (ratMul_words value value)
    (show _ ≤ inflationWordBudget n by dsimp only [value, inflationWordBudget]; omega)
  have dimensionValue : (ratCast n).value = (n : ℚ) := rfl
  simp only [inflation, Traced.bind_events, Traced.bind_value, dimensionValue,
    ratAdd_value, ratMul_value, ratDiv_value, wordsWithin_append]
  exact ⟨dimension, add, mul, den, div, double, addBase, square⟩

theorem inflation_result_bits (n : ℕ) :
    (Code.ofRat (inflation n).value).bits ≤ inflationWordBudget n := by
  have valid := inflation_words n
  simp only [inflation, Traced.bind_events, Traced.bind_value, wordsWithin_append] at valid
  have last := valid.2.2.2.2.2.2.2
  let value : ℚ := 1 + 2 * (1 / (64 * (n : ℚ) * ((n : ℚ) + 1)))
  change WordsWithin (inflationWordBudget n) (ratMul value value).events at last
  let raw := (Code.ofRat value).mul (Code.ofRat value)
  let event : Event := ⟨.normalize, [raw.bits, (Code.ofRat (value * value)).bits]⟩
  have member : event ∈ (ratMul value value).events := by
    change event ∈ [_, event]
    simp
  have result := last event member (Code.ofRat (value * value)).bits (by simp [event])
  rw [inflation_value]
  simpa only [value, stepInflation, stepEta, pow_two] using result

def diagonalWordBudget (n p : ℕ) := n + p + 2 * (n + p + 7) + 20

theorem diagonal_words (n p : ℕ) : WordsWithin (diagonalWordBudget n p) (diagonal n p).events := by
  have dim := natural_rational_bits n
  have power : (Code.ofRat ((2 ^ p : ℕ) : ℚ)).bits = p + 4 := by simp [Code.ofRat, Code.bits, Nat.size_pow]
  have powers := (powerTwo_words p).mono (show p + 2 ≤ diagonalWordBudget n p by dsimp [diagonalWordBudget]; omega)
  have divide := WordsWithin.mono (ratDiv_words (n : ℚ) ((2 ^ p : ℕ) : ℚ))
    (show _ ≤ diagonalWordBudget n p by rw [power]; dsimp [diagonalWordBudget]; omega)
  have ns : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  simp only [diagonal, Traced.bind_events, Traced.bind_value, powerTwo_value, ratCast,
    emit_value, wordsWithin_append]
  refine ⟨powers, ?_, ?_, divide⟩
  all_goals
    simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq, and_true, Nat.size_pow]
    dsimp [diagonalWordBudget]
    omega

theorem diagonal_result_bits (n p : ℕ) :
    (Code.ofRat (diagonal n p).value).bits ≤ diagonalWordBudget n p := by
  have dim := natural_rational_bits n
  have power : (Code.ofRat ((2 ^ p : ℕ) : ℚ)).bits = p + 4 := by simp [Code.ofRat, Code.bits, Nat.size_pow]
  have bound := ratDiv_result_bits (n : ℚ) ((2 ^ p : ℕ) : ℚ)
  rw [power] at bound
  have result : (Code.ofRat ((n : ℚ) / ((2 ^ p : ℕ) : ℚ))).bits ≤ diagonalWordBudget n p := by
    dsimp [diagonalWordBudget]
    omega
  rw [diagonal_value]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using result

end BuyAtBulk.PolynomialLP.Trace
