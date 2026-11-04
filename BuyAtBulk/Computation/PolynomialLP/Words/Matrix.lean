import BuyAtBulk.Computation.PolynomialLP.Trace.Matrix
import BuyAtBulk.Computation.PolynomialLP.MatrixArithmeticBits

/-! Every multiplication, normalized partial sum, array index and output word
of the actual materialized matrix arithmetic has polynomial binary length. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP.Trace
open Computation Computation.Runtime Rational
variable {n : ℕ}

theorem dotScan_bits (a x : Vector ℚ n) (indices : List (Fin n)) (L : ℕ) (constant : 5 ≤ L)
    (aBits : ∀ j : Fin n, (Code.ofRat a[j.val]).bits + 1 ≤ L)
    (xBits : ∀ j : Fin n, (Code.ofRat x[j.val]).bits + 1 ≤ L) :
    (Code.ofRat (dotScan a x indices).value).bits ≤ 2 * (4 * indices.length + 1) * L + 2 := by
  let terms := indices.map fun j => (a[j.val], x[j.val])
  have bound := HelperExpressions.sum_products_bits terms L constant (by
    intro q member
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp member
    exact ⟨aBits j, xBits j⟩)
  simpa only [dotScan_value, terms, List.map_map, Function.comp_def, List.length_map] using bound

def dotWordBudget (n k L : ℕ) := n + 32 * (k + 1) * (L + 2) + 64

theorem dotScan_words (a x : Vector ℚ n) (indices : List (Fin n)) (L : ℕ) (constant : 5 ≤ L)
    (aBits : ∀ j : Fin n, (Code.ofRat a[j.val]).bits + 1 ≤ L)
    (xBits : ∀ j : Fin n, (Code.ofRat x[j.val]).bits + 1 ≤ L) :
    WordsWithin (dotWordBudget n indices.length L) (dotScan a x indices).events := by
  induction indices with
  | nil => exact wordsWithin_nil _
  | cons j rest ih =>
    have ai := aBits j
    have xi := xBits j
    have index : j.val.size ≤ n := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt j.isLt)
    have productBits := ratMul_result_bits a[j.val] x[j.val]
    have tailBits := dotScan_bits a x rest L constant aBits xBits
    have productWords := WordsWithin.mono (ratMul_words a[j.val] x[j.val])
      (show 2 * ((Code.ofRat a[j.val]).bits + (Code.ofRat x[j.val]).bits) + 8 ≤
        dotWordBudget n (j :: rest).length L by dsimp [dotWordBudget]; nlinarith)
    have sumWords := WordsWithin.mono (ratAdd_words (a[j.val] * x[j.val]) (dotScan a x rest).value)
      (show 2 * ((Code.ofRat (a[j.val] * x[j.val])).bits + (Code.ofRat (dotScan a x rest).value).bits) + 8 ≤
        dotWordBudget n (j :: rest).length L by dsimp [dotWordBudget]; nlinarith)
    simp only [dotScan, Traced.bind_events, Traced.bind_value, emit_value, readRat,
      ratMul_value, wordsWithin_append]
    refine ⟨?_, ?_, ?_, productWords, ih.mono ?_, sumWords⟩
    · simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq, and_true]
      dsimp [dotWordBudget]
      nlinarith
    · simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, forall_eq, and_true]
      dsimp [dotWordBudget]
      constructor <;> nlinarith
    · simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, forall_eq, and_true]
      dsimp [dotWordBudget]
      constructor <;> nlinarith
    · dsimp [dotWordBudget]
      nlinarith

def matrixWordBudget (n L : ℕ) := dotWordBudget n n L + matrixProductBudget n L + n

theorem matrixVector_words (shape : Vector (Vector ℚ n) n) (direction : Vector ℚ n)
    (L : ℕ) (constant : 5 ≤ L)
    (shapeBits : ∀ i j : Fin n, (Code.ofRat shape[i.val][j.val]).bits + 1 ≤ L)
    (directionBits : ∀ j : Fin n, (Code.ofRat direction[j.val]).bits + 1 ≤ L) :
    WordsWithin (matrixWordBudget n L) (matrixVector shape direction).events := by
  have rows : ∀ i : Fin n, WordsWithin (matrixWordBudget n L)
      (matrixRow shape direction (List.finRange n) i).events := by
    intro i
    have index : i.val.size ≤ n := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt i.isLt)
    have size : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
    have arithmetic := (dotScan_words shape[i.val] direction (List.finRange n) L constant (shapeBits i) directionBits).mono
      (show dotWordBudget n (List.finRange n).length L ≤ matrixWordBudget n L by
        simp only [List.length_finRange]; dsimp [matrixWordBudget]; omega)
    simp only [matrixRow, Traced.bind_events, Traced.bind_value, emit_value, wordsWithin_append]
    refine ⟨?_, arithmetic⟩
    simp only [emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, and_true]
    dsimp [matrixWordBudget]
    constructor <;> omega
  have values : ∀ i : Fin n,
      (Code.ofRat (matrixRow shape direction (List.finRange n) i).value).bits ≤ matrixWordBudget n L := by
    intro i
    have bit := dotScan_bits shape[i.val] direction (List.finRange n) L constant (shapeBits i) directionBits
    simpa only [List.length_finRange, matrixProductBudget, matrixRow_value, dotScan_value] using
      bit.trans (show 2 * (4 * (List.finRange n).length + 1) * L + 2 ≤ matrixWordBudget n L by
        simp only [List.length_finRange]; dsimp [matrixWordBudget, matrixProductBudget]; omega)
  simp only [matrixVector, wordsWithin_append, indexList_value]
  exact ⟨indexList_words n _ (by dsimp [matrixWordBudget]; omega),
    Weights.materialize_words _ _ _ (by dsimp [matrixWordBudget]; omega) rows values⟩

def quadraticWordBudget (n L : ℕ) :=
  matrixWordBudget n L + dotWordBudget n n (matrixProductBudget n L + L + 5) + n

theorem quadratic_words (shape : Vector (Vector ℚ n) n) (direction : Vector ℚ n)
    (L : ℕ) (constant : 5 ≤ L)
    (shapeBits : ∀ i j : Fin n, (Code.ofRat shape[i.val][j.val]).bits + 1 ≤ L)
    (directionBits : ∀ j : Fin n, (Code.ofRat direction[j.val]).bits + 1 ≤ L) :
    WordsWithin (quadraticWordBudget n L) (quadratic shape direction).events := by
  have image := (matrixVector_words shape direction L constant shapeBits directionBits).mono
    (show matrixWordBudget n L ≤ quadraticWordBudget n L by dsimp [quadraticWordBudget]; omega)
  have directionLarge : ∀ j : Fin n, (Code.ofRat direction[j.val]).bits + 1 ≤ matrixProductBudget n L + L + 5 := by
    intro j
    have bound := directionBits j
    omega
  have imageBits : ∀ j : Fin n,
      (Code.ofRat (matrixVector shape direction).value[j.val]).bits + 1 ≤ matrixProductBudget n L + L + 5 := by
    intro j
    rw [matrixVector_value]
    have bound := PolynomialLP.matrixVector_bits shape direction L constant shapeBits directionBits j
    omega
  have dot := (dotScan_words direction (matrixVector shape direction).value (List.finRange n)
    (matrixProductBudget n L + L + 5) (by omega) directionLarge imageBits).mono
      (show dotWordBudget n (List.finRange n).length (matrixProductBudget n L + L + 5) ≤ quadraticWordBudget n L by
        simp only [List.length_finRange]; dsimp [quadraticWordBudget]; omega)
  simp only [quadratic, wordsWithin_append, indexList_value]
  exact ⟨⟨image, indexList_words n _ (by dsimp [quadraticWordBudget]; omega)⟩, dot⟩

end BuyAtBulk.PolynomialLP.Trace
