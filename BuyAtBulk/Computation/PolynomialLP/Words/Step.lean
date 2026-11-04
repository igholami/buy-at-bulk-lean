import BuyAtBulk.Computation.PolynomialLP.Trace.Loop
import BuyAtBulk.Computation.PolynomialLP.Words.Rounded

/-! Word bounds for all numerical guard branches of the actual ellipsoid
step, including dimension/degeneracy exits. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP.Trace
open Computation Computation.Runtime Rational
variable {n : ℕ}

def stepWordBudget (n p L : ℕ) := roundedWordBudget n p L + quadraticWordBudget n L +
  updateQuadraticBudget n L + n + 10

theorem step_words (state : Ellipsoid n) (direction : Vector ℚ n) (p L : ℕ) (constant : 5 ≤ L)
    (centerBits : ∀ i : Fin n, (Code.ofRat state.center[i.val]).bits + 1 ≤ L)
    (shapeBits : ∀ i j : Fin n, (Code.ofRat state.shape[i.val][j.val]).bits + 1 ≤ L)
    (directionBits : ∀ i : Fin n, (Code.ofRat direction[i.val]).bits + 1 ≤ L) :
    WordsWithin (stepWordBudget n p L) (step state direction p).events := by
  let K := stepWordBudget n p L
  have index : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have zeroBits : (Code.ofRat 0).bits = 3 := by decide
  have qBits := PolynomialLP.quadratic_bits state.shape direction L constant shapeBits directionBits
  change (Code.ofRat (PolynomialLP.quadratic state.shape direction)).bits ≤ updateQuadraticBudget n L at qBits
  have qWords := (quadratic_words state.shape direction L constant shapeBits directionBits).mono
    (show _ ≤ K by dsimp only [K, stepWordBudget]; omega)
  have nextWords := (roundedStep_words state direction p L constant centerBits shapeBits directionBits).mono
    (show _ ≤ K by dsimp only [K, stepWordBudget]; omega)
  have compare : WordsWithin K (emit .natCompare [n.size, 1] (decide (n ≤ 1))).events := by
    simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, and_true]
    dsimp only [K, stepWordBudget]
    constructor <;> omega
  have tag {α : Type} (value : α) : WordsWithin K (emit .branch [1] value).events := by
    simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq, and_true]
    dsimp only [K, stepWordBudget]
    omega
  have write {α : Type} (value : α) : WordsWithin K (emit .write [n.size] value).events := by
    simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq, and_true]
    dsimp only [K, stepWordBudget]
    omega
  have qCompare : WordsWithin K (ratLe (PolynomialLP.quadratic state.shape direction) 0).events := by
    simp only [ratLe, emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, and_true, zeroBits]
    dsimp only [K, stepWordBudget]
    constructor <;> omega
  by_cases small : n ≤ 1
  · simp only [step, Traced.bind_events, Traced.bind_value, emit_value, branch,
      small, decide_true, Bool.true_eq, ite_true, Traced.pure_events, wordsWithin_append,
      wordsWithin_nil, and_true]
    exact ⟨compare, tag _⟩
  · by_cases nonpositive : PolynomialLP.quadratic state.shape direction ≤ 0
    · simp only [step, Traced.bind_events, Traced.bind_value, emit_value, branch,
        small, decide_false, Bool.false_eq_true, ite_false, quadratic_value, ratLe,
        nonpositive, decide_true, Bool.true_eq, ite_true, Traced.pure_events,
        wordsWithin_append, wordsWithin_nil, and_true]
      exact ⟨compare, tag _, qWords, qCompare, tag _⟩
    · simp only [step, Traced.bind_events, Traced.bind_value, emit_value, branch,
        small, decide_false, Bool.false_eq_true, ite_false, quadratic_value, ratLe,
        nonpositive, wordsWithin_append]
      exact ⟨compare, tag _, qWords, qCompare, tag _, nextWords, write _⟩

end BuyAtBulk.PolynomialLP.Trace
