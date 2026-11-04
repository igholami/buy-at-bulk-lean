import BuyAtBulk.Computation.Rational.Expression
import Mathlib.Data.Nat.Log

/-! A closed word-operation vocabulary for instrumented numerical programs.
Events record actual operand widths. No user-supplied cost callback occurs in
the machine; refinements to individual algorithms must be proved separately. -/
namespace BuyAtBulk.Computation.Runtime
open Rational
variable {α β : Type} {n : ℕ}

/-- `scan` includes the constant work of advancing a loop index, testing
its bound, and allocating the current materialized cell. An early-stopping
scan does not pay for an unvisited tail; materialized index lists are charged
separately by `indexList`. `read`/`write` access one indexed scalar cell. -/
inductive Operation where
  | read | write | branch | scan | cons | index | path | recurse
  | ratAdd | ratMul | ratDiv | ratNeg | ratCompare | normalize | ratCast
  | natAdd | natMul | natCompare | natPower | natClog | intDiv | natSub
  | intMul | intAdd | intAbs | intNeg | intCompare | natMod
  deriving DecidableEq, Repr

structure Event where
  operation : Operation
  words : List ℕ
  deriving Repr

structure Traced (α : Type) where
  value : α
  events : List Event

namespace Traced
def pure (value : α) : Traced α := ⟨value, []⟩
def bind (first : Traced α) (next : α → Traced β) : Traced β :=
  let second := next first.value
  ⟨second.value, first.events ++ second.events⟩
instance : Monad Traced where
  pure := pure
  bind := bind

@[simp] theorem pure_value (a : α) : (pure a).value = a := rfl
@[simp] theorem pure_events (a : α) : (pure a).events = [] := rfl
@[simp] theorem bind_value (a : Traced α) (f : α → Traced β) :
    (a >>= f).value = (f a.value).value := rfl
@[simp] theorem bind_events (a : Traced α) (f : α → Traced β) :
    (a >>= f).events = a.events ++ (f a.value).events := rfl
@[simp] theorem ite_value (p : Prop) [Decidable p] (a b : Traced α) :
    (if p then a else b).value = if p then a.value else b.value := by split_ifs <;> rfl
@[simp] theorem ite_events (p : Prop) [Decidable p] (a b : Traced α) :
    (if p then a else b).events = if p then a.events else b.events := by split_ifs <;> rfl
end Traced

def emit (operation : Operation) (words : List ℕ) (value : α) : Traced α :=
  ⟨value, [⟨operation, words⟩]⟩

private def ratBinary (operation : Operation) (a b : ℚ) (raw : Code) (result : ℚ) : Traced ℚ :=
  ⟨result, [⟨operation, [(Code.ofRat a).bits, (Code.ofRat b).bits]⟩,
    ⟨.normalize, [raw.bits, (Code.ofRat result).bits]⟩]⟩
def ratAdd (a b : ℚ) : Traced ℚ := ratBinary .ratAdd a b ((Code.ofRat a).add (Code.ofRat b)) (a + b)
def ratMul (a b : ℚ) : Traced ℚ := ratBinary .ratMul a b ((Code.ofRat a).mul (Code.ofRat b)) (a * b)
def ratDiv (a b : ℚ) : Traced ℚ := ratBinary .ratDiv a b ((Code.ofRat a).div (Code.ofRat b)) (a / b)
def ratLess (a b : ℚ) : Traced Bool := emit .ratCompare [(Code.ofRat a).bits, (Code.ofRat b).bits] (decide (a < b))
def ratLe (a b : ℚ) : Traced Bool := emit .ratCompare [(Code.ofRat a).bits, (Code.ofRat b).bits] (decide (a ≤ b))
def natMul (a b : ℕ) : Traced ℕ := emit .natMul [a.size, b.size] (a * b)
def natClog (a b : ℕ) : Traced ℕ := emit .natClog [a.size, b.size] (Nat.clog a b)
def natPower (a b : ℕ) : Traced ℕ := emit .natPower [a.size, b.size] (a ^ b)
def ratCast (a : ℕ) : Traced ℚ := emit .ratCast [a.size] (a : ℚ)
def branch (condition : Bool) : Traced Bool := emit .branch [1] condition
def readRat (values : Vector ℚ n) (i : Fin n) : Traced ℚ :=
  emit .read [i.val.size, (Code.ofRat values[i.val]).bits] values[i.val]

@[simp] theorem emit_value (operation words) (a : α) : (emit operation words a).value = a := rfl
@[simp] theorem emit_length (operation words) (a : α) : (emit operation words a).events.length = 1 := rfl
@[simp] theorem ratAdd_value (a b : ℚ) : (ratAdd a b).value = a + b := rfl
@[simp] theorem ratMul_value (a b : ℚ) : (ratMul a b).value = a * b := rfl
@[simp] theorem ratDiv_value (a b : ℚ) : (ratDiv a b).value = a / b := rfl
@[simp] theorem ratAdd_length (a b : ℚ) : (ratAdd a b).events.length = 2 := rfl
@[simp] theorem ratMul_length (a b : ℚ) : (ratMul a b).events.length = 2 := rfl
@[simp] theorem ratDiv_length (a b : ℚ) : (ratDiv a b).events.length = 2 := rfl

/-- Raw and normalized addition words have an additive input-width budget.
This includes the unreduced numerator/denominator pair passed to normalization. -/
theorem ratAdd_words (a b : ℚ) :
    ∀ event ∈ (ratAdd a b).events, ∀ word ∈ event.words,
      word ≤ 2 * ((Code.ofRat a).bits + (Code.ofRat b).bits) + 8 := by
  have raw := Code.bounded_bits (Code.add_bounded
    (Code.bounded_of_bits (Code.ofRat a)) (Code.bounded_of_bits (Code.ofRat b)))
  have normalized : (Code.ofRat (a + b)).bits ≤ ((Code.ofRat a).add (Code.ofRat b)).bits := by
    simpa using Code.normalized_bits_le ((Code.ofRat a).add (Code.ofRat b))
  simp only [ratAdd, ratBinary, List.mem_cons, List.not_mem_nil, or_false]
  intro event member
  rcases member with rfl | rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro word member
    rcases member with rfl | rfl <;> omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro word member
    rcases member with rfl | rfl <;> omega

theorem ratAdd_result_bits (a b : ℚ) :
    (Code.ofRat (a + b)).bits ≤ 2 * ((Code.ofRat a).bits + (Code.ofRat b).bits) + 8 := by
  exact ratAdd_words a b ⟨.normalize, [((Code.ofRat a).add (Code.ofRat b)).bits, (Code.ofRat (a+b)).bits]⟩
    (by simp [ratAdd, ratBinary]) _ (by simp)

private theorem binary_words (operation : Operation) (a b : ℚ) (raw : Code) (result : ℚ)
    (decoded : raw.value = result) (raw_bound : raw.bits ≤ 2 * ((Code.ofRat a).bits + (Code.ofRat b).bits) + 8) :
    ∀ event ∈ (ratBinary operation a b raw result).events, ∀ word ∈ event.words,
      word ≤ 2 * ((Code.ofRat a).bits + (Code.ofRat b).bits) + 8 := by
  have normalized : (Code.ofRat result).bits ≤ raw.bits := decoded ▸ Code.normalized_bits_le raw
  simp only [ratBinary, List.mem_cons, List.not_mem_nil, or_false]
  intro event member
  rcases member with rfl | rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro word member
    rcases member with rfl | rfl <;> omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro word member
    rcases member with rfl | rfl <;> omega

theorem ratMul_words (a b : ℚ) :
    ∀ event ∈ (ratMul a b).events, ∀ word ∈ event.words,
      word ≤ 2 * ((Code.ofRat a).bits + (Code.ofRat b).bits) + 8 := by
  apply binary_words
  · simp
  · have raw := Code.bounded_bits (Code.mul_bounded
      (Code.bounded_of_bits (Code.ofRat a)) (Code.bounded_of_bits (Code.ofRat b)))
    omega

theorem ratDiv_words (a b : ℚ) :
    ∀ event ∈ (ratDiv a b).events, ∀ word ∈ event.words,
      word ≤ 2 * ((Code.ofRat a).bits + (Code.ofRat b).bits) + 8 := by
  apply binary_words
  · simp
  · have raw := Code.bounded_bits (Code.div_bounded
      (Code.bounded_of_bits (Code.ofRat a)) (Code.bounded_of_bits (Code.ofRat b)) (by omega))
    omega

theorem ratMul_result_bits (a b : ℚ) :
    (Code.ofRat (a * b)).bits ≤ 2 * ((Code.ofRat a).bits + (Code.ofRat b).bits) + 8 := by
  exact ratMul_words a b ⟨.normalize, [((Code.ofRat a).mul (Code.ofRat b)).bits, (Code.ofRat (a*b)).bits]⟩
    (by simp [ratMul, ratBinary]) _ (by simp)

theorem ratDiv_result_bits (a b : ℚ) :
    (Code.ofRat (a / b)).bits ≤ 2 * ((Code.ofRat a).bits + (Code.ofRat b).bits) + 8 := by
  exact ratDiv_words a b ⟨.normalize, [((Code.ofRat a).div (Code.ofRat b)).bits, (Code.ofRat (a/b)).bits]⟩
    (by simp [ratDiv, ratBinary]) _ (by simp)

def WordsWithin (bound : ℕ) (events : List Event) : Prop :=
  ∀ event ∈ events, ∀ word ∈ event.words, word ≤ bound

@[simp] theorem wordsWithin_nil (bound : ℕ) : WordsWithin bound [] := by simp [WordsWithin]
@[simp] theorem wordsWithin_cons (bound : ℕ) (event : Event) (rest : List Event) :
    WordsWithin bound (event :: rest) ↔
      (∀ word ∈ event.words, word ≤ bound) ∧ WordsWithin bound rest := by
  simp [WordsWithin]
@[simp] theorem wordsWithin_append (bound : ℕ) (first second : List Event) :
    WordsWithin bound (first ++ second) ↔ WordsWithin bound first ∧ WordsWithin bound second := by
  simp [WordsWithin, List.mem_append, or_imp, forall_and]

theorem WordsWithin.mono {a b : ℕ} {events : List Event}
    (h : WordsWithin a events) (bound : a ≤ b) : WordsWithin b events :=
  fun event member word present => (h event member word present).trans bound

/-- Materialize index values and their trace from the same vector cells.
Unlike a prefix search, this pays for the entire allocated index list. -/
def indexList (n : ℕ) : Traced (List (Fin n)) :=
  let cells := Vector.ofFn fun v : Fin n =>
    (⟨v, [⟨Operation.scan, [v.val.size]⟩, ⟨Operation.write, [v.val.size]⟩,
      ⟨Operation.cons, [v.val.size]⟩]⟩ : Traced (Fin n))
  ⟨cells.toList.map Traced.value, cells.toList.flatMap Traced.events⟩

@[simp] theorem indexList_value (n : ℕ) : (indexList n).value = List.finRange n := by
  simp only [indexList, Vector.toList_ofFn, List.map_ofFn]
  change List.ofFn id = List.finRange n
  exact List.ofFn_id n

theorem indexList_count (n : ℕ) : (indexList n).events.length = 3 * n := by
  simp [indexList, Vector.toList_ofFn, List.length_flatMap, List.ofFn_eq_map,
    List.map_map, Function.comp_def, Nat.mul_comm]

theorem indexList_words (n K : ℕ) (indices : n ≤ K) : WordsWithin K (indexList n).events := by
  intro event member word present
  simp only [indexList, Vector.toList_ofFn, List.mem_flatMap, List.mem_ofFn] at member
  obtain ⟨cell, ⟨v, rfl⟩, event_mem⟩ := member
  have vi : v.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt v.isLt |>.trans indices)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at event_mem
  rcases event_mem with rfl | rfl | rfl <;>
    simp only [List.mem_singleton] at present <;> simpa only [present] using vi

end BuyAtBulk.Computation.Runtime
