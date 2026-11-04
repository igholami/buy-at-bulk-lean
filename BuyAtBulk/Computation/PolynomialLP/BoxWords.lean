import BuyAtBulk.Computation.PolynomialLP.BoxTrace

/-! Width bounds for the actual stored box construction. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP.InputTrace
open Computation.Runtime Computation.Rational
variable {n m k : ℕ} {α : Type}

theorem rowWidth_bound (row : Vector ℚ n) (L : ℕ)
    (inputs : ∀ j : Fin n, (Code.ofRat row[j.val]).bits ≤ L) : rowWidth row ≤ n * L := by
  calc
    _ ≤ ((List.finRange n).map fun _ => L).sum :=
      List.sum_le_sum (fun j _ => inputs j)
    _ = _ := by simp

theorem appendVector_width (left : Vector α m) (right : Vector α k) (width : α → ℕ)
    (K : ℕ) (leftWords : ∀ i : Fin m, width left[i.val] ≤ K)
    (rightWords : ∀ j : Fin k, width right[j.val] ≤ K) :
    ∀ i : Fin (m + k), width (appendVector left right width).value[i.val] ≤ K := by
  intro i
  apply Fin.addCases (motive := fun i => width (appendVector left right width).value[i.val] ≤ K) _ _ i
  · intro j
    change width (left ++ right)[j.val] ≤ K
    rw [Vector.getElem_append_left j.isLt]
    exact leftWords j
  · intro j
    change width (left ++ right)[m + j.val] ≤ K
    rw [Vector.getElem_append_right (by omega) (by omega)]
    simpa only [Nat.add_sub_cancel_left] using rightWords j

theorem coordinateRows_width (n : ℕ) (sign : ℚ) (L : ℕ)
    (input : (Code.ofRat sign).bits ≤ L) (i : Fin n) :
    rowWidth (coordinateRowsTrace n sign).value[i.val] ≤ n * (L + 3) := by
  apply rowWidth_bound
  intro j
  simp only [coordinateRowsTrace_value, coordinateRows, Vector.getElem_ofFn]
  exact conditional_bits sign (i = j) L input

def boxedWordBudget (n m L : ℕ) : ℕ := m + 4 * n + n * (L + 5) + L + 30

theorem boxedTrace_words (input : Stored (n := n) (m := m)) (L : ℕ)
    (coefficients : ∀ i : Fin m, ∀ j : Fin n, (Code.ofRat input.coefficients[i.val][j.val]).bits ≤ L)
    (bounds : ∀ i : Fin m, (Code.ofRat input.bounds[i.val]).bits ≤ L) :
    WordsWithin (boxedWordBudget n m L) (boxedTrace input).events := by
  let K := boxedWordBudget n m L
  let upper := (coordinateRowsTrace n 1).value
  let lower := (coordinateRowsTrace n (-1)).value
  let ones := (replicateTrace n 1).value
  let zeros := (replicateTrace n 0).value
  let newRows := (appendVector upper lower rowWidth).value
  let newBounds := (appendVector ones zeros (fun q : ℚ => (Code.ofRat q).bits)).value
  have oneBits : (Code.ofRat 1).bits = 4 := by decide
  have negBits : (Code.ofRat (-1)).bits = 4 := by decide
  have zeroBits : (Code.ofRat 0).bits = 3 := by decide
  have upperWidth : ∀ i : Fin n, rowWidth upper[i.val] ≤ K := by
    intro i
    have width := coordinateRows_width n 1 4 (by omega) i
    dsimp [upper] at *
    dsimp [K, boxedWordBudget]
    nlinarith
  have lowerWidth : ∀ i : Fin n, rowWidth lower[i.val] ≤ K := by
    intro i
    have width := coordinateRows_width n (-1) 4 (by omega) i
    dsimp [lower] at *
    dsimp [K, boxedWordBudget]
    nlinarith
  have onesWidth : ∀ i : Fin n, (Code.ofRat ones[i.val]).bits ≤ K := by
    intro i
    simp only [ones, replicateTrace_value, Vector.getElem_replicate, oneBits]
    dsimp [K, boxedWordBudget]
    omega
  have zerosWidth : ∀ i : Fin n, (Code.ofRat zeros[i.val]).bits ≤ K := by
    intro i
    simp only [zeros, replicateTrace_value, Vector.getElem_replicate, zeroBits]
    dsimp [K, boxedWordBudget]
    omega
  have newRowsWidth := appendVector_width upper lower rowWidth K upperWidth lowerWidth
  have newBoundsWidth := appendVector_width ones zeros (fun q : ℚ => (Code.ofRat q).bits) K onesWidth zerosWidth
  have oldRowsWidth : ∀ i : Fin m, rowWidth input.coefficients[i.val] ≤ K := by
    intro i
    have width := rowWidth_bound input.coefficients[i.val] L (coefficients i)
    dsimp [K, boxedWordBudget]
    nlinarith
  have oldBoundsWidth : ∀ i : Fin m, (Code.ofRat input.bounds[i.val]).bits ≤ K := by
    intro i
    have width := bounds i
    dsimp [K, boxedWordBudget]
    omega
  have upperWords := (coordinateRowsTrace_words n 1 4 (by omega)).mono
    (show n + n * (4 + 3) + 4 + 10 ≤ K by dsimp [K, boxedWordBudget]; nlinarith)
  have lowerWords := (coordinateRowsTrace_words n (-1) 4 (by omega)).mono
    (show n + n * (4 + 3) + 4 + 10 ≤ K by dsimp [K, boxedWordBudget]; nlinarith)
  have rowAppend := appendVector_words upper lower rowWidth K
    (by dsimp [K, boxedWordBudget]; omega) upperWidth lowerWidth
  have onesWords := (replicateTrace_words n 1).mono (show n + (Code.ofRat 1).bits ≤ K by
    rw [oneBits]; dsimp [K, boxedWordBudget]; omega)
  have zerosWords := (replicateTrace_words n 0).mono (show n + (Code.ofRat 0).bits ≤ K by
    rw [zeroBits]; dsimp [K, boxedWordBudget]; omega)
  have boundAppend := appendVector_words ones zeros (fun q : ℚ => (Code.ofRat q).bits) K
    (by dsimp [K, boxedWordBudget]; omega) onesWidth zerosWidth
  have coefficientsAppend := appendVector_words input.coefficients newRows rowWidth K
    (by dsimp [K, boxedWordBudget]; omega) oldRowsWidth newRowsWidth
  have boundsAppend := appendVector_words input.bounds newBounds (fun q : ℚ => (Code.ofRat q).bits) K
    (by dsimp [K, boxedWordBudget]; omega) oldBoundsWidth newBoundsWidth
  have ni : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have mi : m.size ≤ m := Nat.size_le.mpr Nat.lt_two_pow_self
  change WordsWithin K _
  simp only [boxedTrace, Traced.bind_events, Traced.bind_value, emit_value, wordsWithin_append]
  refine ⟨upperWords, lowerWords, rowAppend, onesWords, zerosWords, boundAppend,
    coefficientsAppend, boundsAppend, ?_, ?_⟩
  all_goals
    simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, and_true]
    dsimp [K, boxedWordBudget]
    repeat' apply And.intro
    all_goals omega

end BuyAtBulk.PolynomialLP.InputTrace
