import BuyAtBulk.Computation.Runtime.Primitive

/-! One-time rational decode/cache. The raw numerator/denominator code passed
to normalization and the normalized result are both present in the trace. -/
set_option maxHeartbeats 1800000
namespace BuyAtBulk.Computation.Runtime.Original
open Rational
variable {n : ℕ}

def integerCast (z : ℤ) : Traced ℚ := emit .ratCast [z.natAbs.size + 1] (z : ℚ)

def decodeRat (q : Code) : Traced ℚ :=
  let numerator := integerCast q.numerator
  let denominator := integerCast q.denominator
  let result := ratDiv numerator.value denominator.value
  ⟨result.value,
    [⟨Operation.read, [q.numerator.natAbs.size + 1]⟩, ⟨.read, [q.denominator.natAbs.size + 1]⟩] ++
      numerator.events ++ denominator.events ++ result.events ++ [⟨.write, [(Code.ofRat result.value).bits]⟩]⟩

@[simp] theorem decodeRat_value (q : Code) : (decodeRat q).value = q.value := rfl
@[simp] theorem decodeRat_count (q : Code) : (decodeRat q).events.length = 7 := rfl

theorem integerCode_bits (z : ℤ) : (Code.ofRat (z : ℚ)).bits = z.natAbs.size + 3 := by
  simp [Code.bits, Code.ofRat]

theorem decoded_raw (q : Code) :
    (Code.ofRat (q.numerator : ℚ)).div (Code.ofRat (q.denominator : ℚ)) = q := by
  rcases q with ⟨numerator, denominator, nonzero⟩
  simp [Code.ofRat, Code.div, Code.mul, Code.inv, nonzero]

theorem decodeRat_normalized_bits (q : Code) : (Code.ofRat (decodeRat q).value).bits ≤ q.bits :=
  Code.normalized_bits_le q

theorem decodeRat_words (q : Code) : WordsWithin (q.bits + 3) (decodeRat q).events := by
  have numerator : (Code.ofRat (q.numerator : ℚ)).bits ≤ q.bits + 3 := by
    rw [integerCode_bits]
    unfold Code.bits
    omega
  have denominator : (Code.ofRat (q.denominator : ℚ)).bits ≤ q.bits + 3 := by
    rw [integerCode_bits]
    unfold Code.bits
    omega
  have normalized := decodeRat_normalized_bits q
  have division_events : (ratDiv (q.numerator : ℚ) (q.denominator : ℚ)).events =
      [⟨Operation.ratDiv, [(Code.ofRat (q.numerator : ℚ)).bits, (Code.ofRat (q.denominator : ℚ)).bits]⟩,
       ⟨Operation.normalize, [q.bits, (Code.ofRat q.value).bits]⟩] := by
    change [(⟨Operation.ratDiv, _⟩ : Event), ⟨Operation.normalize, [_ , _]⟩] = _
    rw [decoded_raw]
    rfl
  have numerator_field : q.numerator.natAbs.size + 1 ≤ q.bits + 3 := by unfold Code.bits; omega
  have denominator_field : q.denominator.natAbs.size + 1 ≤ q.bits + 3 := by unfold Code.bits; omega
  simp_all [decodeRat, integerCast, emit, division_events, wordsWithin_append, wordsWithin_cons, Code.value]
  all_goals omega

def decodeCell (values : Vector Code n) (i : Fin n) : Traced ℚ :=
  let q := values[i.val]
  let decoded := decodeRat q
  ⟨decoded.value, [⟨Operation.scan, [i.val.size]⟩, ⟨.read, [i.val.size, q.bits]⟩] ++
    decoded.events ++ [⟨.write, [i.val.size, (Code.ofRat decoded.value).bits]⟩]⟩

@[simp] theorem decodeCell_value (values : Vector Code n) (i : Fin n) :
    (decodeCell values i).value = values[i.val].value := rfl
@[simp] theorem decodeCell_count (values : Vector Code n) (i : Fin n) :
    (decodeCell values i).events.length = 10 := rfl

theorem decodeCell_words (values : Vector Code n) (i : Fin n) (K : ℕ) (dimension : n ≤ K)
    (input : values[i.val].bits + 3 ≤ K) : WordsWithin K (decodeCell values i).events := by
  have decoded := (decodeRat_words values[i.val]).mono input
  have normalized := decodeRat_normalized_bits values[i.val]
  have index : i.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := i.isLt; omega)
  simp_all [decodeCell, wordsWithin_append, wordsWithin_cons]
  all_goals omega

def decodeVector (values : Vector Code n) : Traced (Vector ℚ n) :=
  let indices := indexList n
  let cells := Vector.ofFn (decodeCell values)
  ⟨cells.map Traced.value,
    indices.events ++ [⟨.write, [n.size]⟩] ++ indices.value.flatMap (fun i => cells[i.val].events)⟩

@[simp] theorem decodeVector_value (values : Vector Code n) (i : Fin n) :
    (decodeVector values).value[i.val] = values[i.val].value := by simp [decodeVector]

theorem decodeVector_count (values : Vector Code n) : (decodeVector values).events.length = 13 * n + 1 := by
  simp [decodeVector, indexList_count, List.length_flatMap, Nat.mul_comm]
  omega

theorem decodeVector_words (values : Vector Code n) (K : ℕ) (dimension : n ≤ K)
    (inputs : ∀ i : Fin n, values[i.val].bits + 3 ≤ K) : WordsWithin K (decodeVector values).events := by
  have indices := indexList_words n K dimension
  have dimension_word : n.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans dimension
  simp only [decodeVector, wordsWithin_append, wordsWithin_cons, wordsWithin_nil, indexList_value, Vector.getElem_ofFn]
  refine ⟨⟨indices, by simpa using dimension_word⟩, ?_⟩
  intro event member word present
  obtain ⟨i, _, cell_mem⟩ := List.mem_flatMap.mp member
  exact decodeCell_words values i K dimension (inputs i) event cell_mem word present

end BuyAtBulk.Computation.Runtime.Original
