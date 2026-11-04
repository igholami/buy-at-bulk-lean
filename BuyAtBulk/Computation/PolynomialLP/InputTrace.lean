import BuyAtBulk.Computation.PolynomialLP.IntegerData
import BuyAtBulk.Computation.Runtime.Primitive
import BuyAtBulk.Computation.Runtime.Weights

/-! Explicit binary-length scanning for the actual stored LP encoding.
The bit budget is computed from integer data, without an uncharged length or
logarithm oracle. Each division halves its actual integer operand. -/
namespace BuyAtBulk.PolynomialLP.InputTrace
open Computation.Runtime Computation.Rational

def bitLength (value : ℕ) : Traced ℕ :=
  if value = 0 then
    ⟨0, [⟨.natCompare, [value.size, 0]⟩, ⟨.branch, [1]⟩, ⟨.write, [0]⟩]⟩
  else
    let next := bitLength (value / 2)
    ⟨next.value + 1,
      [⟨.natCompare, [value.size, 0]⟩, ⟨.branch, [1]⟩,
       ⟨.intDiv, [value.size, 2, (value / 2).size]⟩, ⟨.recurse, [value.size]⟩] ++
      next.events ++ [⟨.natAdd, [next.value.size, 1, (next.value + 1).size]⟩,
        ⟨.write, [(next.value + 1).size]⟩]⟩
termination_by value
decreasing_by
  apply Nat.div_lt_self
  · omega
  · decide

theorem bitLength_value (value : ℕ) : (bitLength value).value = value.size := by
  induction value using Nat.binaryRec' with
  | zero => simp [bitLength]
  | bit b value nonzero ih =>
    have ne : Nat.bit b value ≠ 0 := Nat.bit_ne_zero_iff.mpr nonzero
    rw [bitLength]
    simp only [ne, ite_false, Nat.bit_div_two, ih, Nat.size_bit ne, Nat.succ_eq_add_one]

theorem bitLength_count (value : ℕ) : (bitLength value).events.length = 6 * value.size + 3 := by
  induction value using Nat.binaryRec' with
  | zero => simp [bitLength]
  | bit b value nonzero ih =>
    have ne : Nat.bit b value ≠ 0 := Nat.bit_ne_zero_iff.mpr nonzero
    rw [bitLength]
    simp only [ne, ite_false, Nat.bit_div_two, List.length_append, List.length_cons,
      List.length_nil, ih, Nat.size_bit ne]
    omega

theorem bitLength_words (value : ℕ) : WordsWithin (value.size + 2) (bitLength value).events := by
  induction value using Nat.binaryRec' with
  | zero => simp [bitLength, WordsWithin]
  | bit b value nonzero ih =>
    have ne : Nat.bit b value ≠ 0 := Nat.bit_ne_zero_iff.mpr nonzero
    have oldSize : value.size.size ≤ value.size := Nat.size_le.mpr Nat.lt_two_pow_self
    have nextSize : (value.size + 1).size ≤ value.size + 1 := Nat.size_le.mpr Nat.lt_two_pow_self
    rw [bitLength]
    simp only [ne, ite_false, Nat.bit_div_two, bitLength_value, Nat.size_bit ne,
      wordsWithin_append]
    refine ⟨⟨?_, ih.mono (by omega)⟩, ?_⟩
    all_goals
      simp only [wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, forall_eq, and_true]
      repeat' apply And.intro
      all_goals omega

def codeBits (q : ℚ) : Traced ℕ := do
  let signed ← emit .read [q.num.natAbs.size + 1] q.num
  let numerator ← emit .intAbs [signed.natAbs.size + 1, signed.natAbs.size] signed.natAbs
  let denominator ← emit .read [q.den.size] q.den
  let a ← bitLength numerator
  let b ← bitLength denominator
  let sum ← emit .natAdd [a.size, b.size, (a + b).size] (a + b)
  emit .natAdd [sum.size, 2, (sum + 2).size] (sum + 2)

@[simp] theorem codeBits_value (q : ℚ) : (codeBits q).value = (Code.ofRat q).bits := by
  simp [codeBits, Code.bits, Code.ofRat, bitLength_value]

theorem codeBits_count (q : ℚ) : (codeBits q).events.length ≤ 6 * (Code.ofRat q).bits + 10 := by
  simp only [codeBits, Traced.bind_events, Traced.bind_value, emit_value, List.length_append,
    emit_length, bitLength_count, bitLength_value, Code.bits, Code.ofRat, Int.natAbs_natCast]
  omega

theorem codeBits_words (q : ℚ) : WordsWithin ((Code.ofRat q).bits + 2) (codeBits q).events := by
  have representation : (Code.ofRat q).bits = q.num.natAbs.size + q.den.size + 2 := by
    simp [Code.bits, Code.ofRat]
  have a := Nat.size_le.mpr (Nat.lt_two_pow_self (n := q.num.natAbs.size))
  have b := Nat.size_le.mpr (Nat.lt_two_pow_self (n := q.den.size))
  have sum := Nat.size_le.mpr (Nat.lt_two_pow_self (n := q.num.natAbs.size + q.den.size))
  have total := Nat.size_le.mpr (Nat.lt_two_pow_self (n := q.num.natAbs.size + q.den.size + 2))
  have numerator := (bitLength_words q.num.natAbs).mono
    (show q.num.natAbs.size + 2 ≤ (Code.ofRat q).bits + 2 by omega)
  have denominator := (bitLength_words q.den).mono
    (show q.den.size + 2 ≤ (Code.ofRat q).bits + 2 by omega)
  simp only [codeBits, Traced.bind_events, Traced.bind_value, emit_value, bitLength_value,
    wordsWithin_append, emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
  repeat' apply And.intro
  all_goals first | exact numerator | exact denominator | omega

end BuyAtBulk.PolynomialLP.InputTrace
