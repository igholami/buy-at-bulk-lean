import BuyAtBulk.Computation.PolynomialLP.SquareRoot

/-! Dyadic-grid invariants for the actual square-root bisection. These give
additive endpoint encoding bounds in the iteration count. -/
namespace BuyAtBulk.PolynomialLP
open Computation.Rational

def OnSqrtGrid (q : ℚ) (age : ℕ) (value : ℚ) : Prop :=
  ∃ k : ℕ, k ≤ 2 ^ age ∧ value = (q + 1) * (k : ℚ) / (2 : ℚ) ^ age

theorem onSqrtGrid_zero (q : ℚ) : OnSqrtGrid q 0 0 := by
  exact ⟨0, by norm_num, by simp⟩
theorem onSqrtGrid_upper (q : ℚ) : OnSqrtGrid q 0 (q + 1) := by
  exact ⟨1, by norm_num, by simp⟩

theorem OnSqrtGrid.next {q value : ℚ} {age : ℕ} (grid : OnSqrtGrid q age value) :
    OnSqrtGrid q (age + 1) value := by
  obtain ⟨k, bound, rfl⟩ := grid
  refine ⟨2 * k, ?_, ?_⟩
  · rw [pow_succ]; omega
  · push_cast
    rw [pow_succ]
    ring

theorem OnSqrtGrid.midpoint {q lower upper : ℚ} {age : ℕ}
    (left : OnSqrtGrid q age lower) (right : OnSqrtGrid q age upper) :
    OnSqrtGrid q (age + 1) ((lower + upper) / 2) := by
  obtain ⟨k, kb, rfl⟩ := left
  obtain ⟨l, lb, rfl⟩ := right
  refine ⟨k + l, ?_, ?_⟩
  · rw [pow_succ]; omega
  · push_cast
    rw [pow_succ]
    ring

theorem OnSqrtGrid.bits {q value : ℚ} {age B : ℕ}
    (grid : OnSqrtGrid q age value) (input : (Code.ofRat q).Bounded B) :
    (Code.ofRat value).bits ≤ 2 * (B + 2 * age + 4) + 2 := by
  obtain ⟨k, kb, rfl⟩ := grid
  let index : Code := ⟨k, 1, by decide⟩
  let scale : Code := ⟨1, (2 : ℤ) ^ age, pow_ne_zero _ (by decide)⟩
  have ib : index.Bounded (age + 1) := by
    constructor
    · change k < 2 ^ (age + 1)
      exact kb.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))
    · change (1 : ℕ) < 2 ^ (age + 1)
      exact Nat.one_lt_pow (by omega) (by decide)
  have sb : scale.Bounded (age + 1) := by
    constructor
    · change (1 : ℕ) < 2 ^ (age + 1)
      exact Nat.one_lt_pow (by omega) (by decide)
    · change ((2 : ℤ) ^ age).natAbs < 2 ^ (age + 1)
      rw [Int.natAbs_pow]
      norm_num
      exact Nat.pow_lt_pow_right (by decide) (by omega)
  have one : (Code.ofRat 1).Bounded 1 := by norm_num [Code.Bounded, Code.ofRat]
  let raw := (((Code.ofRat q).add (Code.ofRat 1)).mul index).mul scale
  have rb : raw.Bounded (B + 2 * age + 4) := by
    have bound := Code.mul_bounded (Code.mul_bounded (Code.add_bounded input one) ib) sb
    convert bound using 1 <;> omega
  have decoded : raw.value = (q + 1) * (k : ℚ) / (2 : ℚ) ^ age := by
    simp only [raw, Code.mul_value, Code.add_value, Code.ofRat_value]
    simp [index, scale, Code.value, div_eq_mul_inv]
  rw [← decoded]
  exact (Code.normalized_bits_le raw).trans (Code.bounded_bits rb)

theorem sqrtBisect_grid (q : ℚ) (fuel age : ℕ) (lower upper : ℚ)
    (left : OnSqrtGrid q age lower) (right : OnSqrtGrid q age upper) :
    OnSqrtGrid q (age + fuel) (sqrtBisect q fuel lower upper).value.1 ∧
    OnSqrtGrid q (age + fuel) (sqrtBisect q fuel lower upper).value.2 := by
  induction fuel generalizing age lower upper with
  | zero => simpa only [Nat.add_zero, sqrtBisect, Computation.Runtime.Traced.pure_value] using And.intro left right
  | succ fuel ih =>
    rw [sqrtBisect_succ]
    split_ifs
    · simpa only [Nat.add_assoc, Nat.add_comm 1 fuel] using
        ih (age + 1) ((lower + upper) / 2) upper (left.midpoint right) right.next
    · simpa only [Nat.add_assoc, Nat.add_comm 1 fuel] using
        ih (age + 1) lower ((lower + upper) / 2) left.next (left.midpoint right)

open Computation.Runtime

theorem midpoint_words (lower upper : ℚ) (E : ℕ)
    (left : (Code.ofRat lower).bits ≤ E) (right : (Code.ofRat upper).bits ≤ E) :
    WordsWithin (16 * E + 64) (midpoint lower upper).events := by
  have sum := ratAdd_result_bits lower upper
  have two : (Code.ofRat 2).bits = 5 := by decide
  simp only [midpoint, Traced.bind_events, Traced.bind_value, ratAdd_value,
    wordsWithin_append]
  constructor
  · exact WordsWithin.mono (ratAdd_words lower upper) (by omega)
  · exact WordsWithin.mono (ratDiv_words (lower + upper) 2) (by omega)

theorem sqrtBisect_words (q : ℚ) (fuel age B : ℕ) (lower upper : ℚ)
    (input : (Code.ofRat q).Bounded B)
    (left : OnSqrtGrid q age lower) (right : OnSqrtGrid q age upper) :
    WordsWithin (128 * (B + age + fuel + 2) + 256)
      (sqrtBisect q fuel lower upper).events := by
  induction fuel generalizing age lower upper with
  | zero => exact wordsWithin_nil _
  | succ fuel ih =>
    have lb := left.bits input
    have ub := right.bits input
    have mid := left.midpoint right
    have mb := mid.bits input
    have qb := Code.bounded_bits input
    have sb := ratMul_result_bits ((lower + upper) / 2) ((lower + upper) / 2)
    have recurseBits : fuel.size ≤ fuel := Nat.size_le.mpr (Nat.lt_two_pow_self)
    have recursiveLeft := ih (age + 1) ((lower + upper) / 2) upper mid right.next
    have recursiveRight := ih (age + 1) lower ((lower + upper) / 2) left.next mid
    have middle := (midpoint_words lower upper _ lb ub).mono
      (show 16 * (2 * (B + 2 * age + 4) + 2) + 64 ≤
        128 * (B + age + (fuel + 1) + 2) + 256 by omega)
    have square := WordsWithin.mono (ratMul_words ((lower + upper) / 2) ((lower + upper) / 2))
      (show 2 * ((Code.ofRat ((lower + upper) / 2)).bits +
        (Code.ofRat ((lower + upper) / 2)).bits) + 8 ≤
        128 * (B + age + (fuel + 1) + 2) + 256 by omega)
    simp only [sqrtBisect, Traced.bind_events, Traced.bind_value, emit_value,
      midpoint_value, ratMul_value, ratLe, branch, wordsWithin_append]
    refine ⟨?_, middle, square, ?_, ?_, ?_⟩
    · simp only [emit, wordsWithin_cons, wordsWithin_nil, and_true, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq]
      omega
    · simp only [emit, wordsWithin_cons, wordsWithin_nil, and_true, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq, forall_eq_or_imp]
      constructor <;> omega
    · simp only [emit, wordsWithin_cons, wordsWithin_nil, and_true, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq]
      omega
    · change WordsWithin _ (if decide ((lower + upper) / 2 * ((lower + upper) / 2) ≤ q) then
        sqrtBisect q fuel ((lower + upper) / 2) upper else
        sqrtBisect q fuel lower ((lower + upper) / 2)).events
      split_ifs with condition
      · convert recursiveLeft using 1 <;> omega
      · convert recursiveRight using 1 <;> omega

theorem sqrtBracket_words (q : ℚ) (precision B : ℕ)
    (input : (Code.ofRat q).Bounded B) :
    WordsWithin (128 * (B + precision + 2) + 256) (sqrtBracket q precision).events := by
  have initial := sqrtBisect_words q precision 0 B 0 (q + 1) input
    (onSqrtGrid_zero q) (onSqrtGrid_upper q)
  have qb := Code.bounded_bits input
  have one : (Code.ofRat 1).bits = 4 := by decide
  simp only [sqrtBracket, Traced.bind_events, Traced.bind_value, ratAdd_value,
    wordsWithin_append]
  constructor
  · exact WordsWithin.mono (ratAdd_words q 1) (by omega)
  · simpa only [Nat.add_zero] using initial

theorem sqrtBracket_endpoint_bits (q : ℚ) (precision B : ℕ)
    (input : (Code.ofRat q).Bounded B) :
    (Code.ofRat (sqrtBracket q precision).value.1).bits ≤ 2 * (B + 2 * precision + 4) + 2 ∧
    (Code.ofRat (sqrtBracket q precision).value.2).bits ≤ 2 * (B + 2 * precision + 4) + 2 := by
  have grid := sqrtBisect_grid q precision 0 0 (q + 1)
    (onSqrtGrid_zero q) (onSqrtGrid_upper q)
  simpa only [sqrtBracket, Traced.bind_value, ratAdd_value, Nat.zero_add] using
    And.intro (grid.1.bits input) (grid.2.bits input)

end BuyAtBulk.PolynomialLP
