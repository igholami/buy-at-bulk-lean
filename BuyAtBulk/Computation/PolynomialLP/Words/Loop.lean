import BuyAtBulk.Computation.PolynomialLP.Words.Step
import BuyAtBulk.Computation.PolynomialLP.Words.Separation

/-! Uniform all-word bounds along the complete actual ellipsoid loop.
Successful-update invariants do not require the constraint region nonempty. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP.Trace
open Computation Computation.Runtime Rational
variable {n m : ℕ}

def loopWordBudget (n m rounds S : ℕ) := separationWordBudget n m S +
  stepWordBudget n (workPrecision n rounds) S + m + n + rounds + 10

theorem loop_words (input : Stored (n := n) (m := m)) (rounds fuel age S : ℕ)
    (constant : 5 ≤ S)
    (coefficients : ∀ i : Fin m, ∀ j : Fin n, (Code.ofRat input.coefficients[i.val][j.val]).bits + 1 ≤ S)
    (bounds : ∀ i : Fin m, (Code.ofRat input.bounds[i.val]).bits + 1 ≤ S)
    (encoding : 2 * (n + 1 + 4 * (rounds + 1) + workPrecision n rounds + 1) + 3 ≤ S)
    (state : Ellipsoid n) (elapsed : age + fuel ≤ rounds) (valid : EllipsoidInvariant state age)
    (centerBits : ∀ i : Fin n, (Code.ofRat state.center[i.val]).bits + 1 ≤ S)
    (shapeBits : ∀ i j : Fin n, (Code.ofRat state.shape[i.val][j.val]).bits + 1 ≤ S) :
    WordsWithin (loopWordBudget n m rounds S) (loop input (workPrecision n rounds) fuel state).events := by
  let K := loopWordBudget n m rounds S
  have ni : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have tag {α : Type} (value : α) : WordsWithin K (emit .branch [1] value).events := by
    simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq, and_true]
    dsimp only [K, loopWordBudget]
    omega
  have write {α : Type} (value : α) : WordsWithin K (emit .write [n.size] value).events := by
    simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq, and_true]
    dsimp only [K, loopWordBudget]
    omega
  induction fuel generalizing age state with
  | zero => exact write _
  | succ fuel ih =>
    have fuelSize : fuel.size ≤ fuel := Nat.size_le.mpr Nat.lt_two_pow_self
    have recurse : WordsWithin K (emit .recurse [fuel.size] ()).events := by
      simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq, and_true]
      dsimp only [K, loopWordBudget]
      omega
    have separation := (separate_words input state.center S constant coefficients bounds centerBits).mono
      (show _ ≤ K by dsimp only [K, loopWordBudget]; omega)
    have perrow (row : Fin m) := (step_words state input.coefficients[row.val] (workPrecision n rounds)
      S constant centerBits shapeBits (coefficients row)).mono
        (show _ ≤ K by dsimp only [K, loopWordBudget]; omega)
    simp only [loop, Traced.bind_events, Traced.bind_value, emit_value, separate_value, wordsWithin_append]
    refine ⟨recurse, separation, tag _, ?_⟩
    cases separated : (PolynomialLP.separate input state.center).value with
    | none => exact write _
    | some row =>
      have index : row.val.size ≤ m := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt row.isLt)
      have read : WordsWithin K (emit .read [row.val.size, n.size] input.coefficients[row.val]).events := by
        simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
          or_false, forall_eq_or_imp, forall_eq, and_true]
        dsimp only [K, loopWordBudget]
        constructor <;> omega
      simp only [Traced.bind_events, Traced.bind_value, emit_value, step_value, wordsWithin_append]
      refine ⟨read, perrow row, tag _, ?_⟩
      cases stepped : state.step input.coefficients[row.val] (workPrecision n rounds) with
      | none => exact write _
      | some next =>
        have nextValid := step_success_invariant state next input.coefficients[row.val] rounds age
          (by omega) valid stepped
        have nextBits := step_success_encoding state next input.coefficients[row.val] rounds age
          (by omega) valid stepped
        exact ih (age + 1) next (by omega) nextValid
          (by intro i; have bound := nextBits.1 i; omega)
          (by intro i j; have bound := nextBits.2 i j; omega)

end BuyAtBulk.PolynomialLP.Trace
