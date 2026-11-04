import BuyAtBulk.Computation.Runtime.Primitive
import BuyAtBulk.Computation.FlowDecomposition.Denominators

/-! Full nonnegative unit-mass rational summation, including actual unreduced
addition operands. A common input denominator prevents exponential word growth. -/
set_option maxHeartbeats 1800000
namespace BuyAtBulk.Computation.Runtime.Original
open Rational BuyAtBulk.Computation.FlowDecomposition

def ratSum : List ℚ → Traced ℚ
  | [] => ⟨0, [⟨.branch, [1]⟩, ⟨.write, [(Code.ofRat 0).bits]⟩]⟩
  | q :: rest =>
    let tail := ratSum rest
    let result := ratAdd q tail.value
    ⟨result.value, [⟨Operation.branch, [1]⟩, ⟨.scan, [1]⟩, ⟨.read, [(Code.ofRat q).bits]⟩] ++
      tail.events ++ result.events ++ [⟨.write, [(Code.ofRat result.value).bits]⟩]⟩

@[simp] theorem ratSum_value (values : List ℚ) : (ratSum values).value = values.sum := by
  induction values <;> simp_all [ratSum]

theorem ratSum_count (values : List ℚ) : (ratSum values).events.length = 6 * values.length + 2 := by
  induction values <;> simp_all [ratSum] <;> omega

theorem add_denominator (D : ℕ) (q r : ℚ) (hq : HasDenominator D q) (hr : HasDenominator D r) :
    HasDenominator D (q + r) :=
  (Rat.add_den_dvd_lcm q r).trans (Nat.lcm_dvd hq hr)

theorem sum_denominator (D : ℕ) (values : List ℚ)
    (inputs : ∀ q ∈ values, HasDenominator D q) : HasDenominator D values.sum := by
  induction values with
  | nil => simp [HasDenominator]
  | cons q rest ih =>
    exact add_denominator D q rest.sum (inputs q (by simp)) (ih (fun r mem => inputs r (by simp [mem])))

theorem ratSum_words (D : ℕ) (positive : 0 < D) (values : List ℚ)
    (denominator : ∀ q ∈ values, HasDenominator D q)
    (nonneg : ∀ q ∈ values, 0 ≤ q) (mass : values.sum ≤ 1) :
    WordsWithin (8 * D.size + 16) (ratSum values).events := by
  revert denominator nonneg mass
  induction values with
  | nil =>
    intro _ _ _
    simp [ratSum, WordsWithin, Code.bits, Code.ofRat]
  | cons q rest ih =>
    intro denominator nonneg mass
    have qlower := nonneg q (by simp)
    have taillower : 0 ≤ rest.sum := List.sum_nonneg (fun r mem => nonneg r (by simp [mem]))
    have qupper : q ≤ 1 := by simp only [List.sum_cons] at mass; linarith
    have tailupper : rest.sum ≤ 1 := by simp only [List.sum_cons] at mass; linarith
    have qbits := unit_bits_bound q D positive (denominator q (by simp)) qlower qupper
    have tailden := sum_denominator D rest (fun r mem => denominator r (by simp [mem]))
    have tailbits := unit_bits_bound rest.sum D positive tailden taillower tailupper
    have resultden := add_denominator D q rest.sum (denominator q (by simp)) tailden
    have resultbits := unit_bits_bound (q + rest.sum) D positive resultden (add_nonneg qlower taillower)
      (by simpa only [List.sum_cons] using mass)
    have tailwords := ih (fun r mem => denominator r (by simp [mem]))
      (fun r mem => nonneg r (by simp [mem])) tailupper
    have addition : WordsWithin (8 * D.size + 16) (ratAdd q rest.sum).events := by
      intro event member word present
      exact (ratAdd_words q rest.sum event member word present).trans (by omega)
    have qbound : (Code.ofRat q).bits ≤ 8 * D.size + 16 := by omega
    have resultbound : (Code.ofRat (q + rest.sum)).bits ≤ 8 * D.size + 16 := by omega
    simp_all [ratSum, wordsWithin_append, wordsWithin_cons]

def inputDenominator (weights : List ℚ) : ℕ := (weights.map Rat.den).prod

def denominatorBits (weights : List ℚ) : ℕ := (weights.map fun q => q.den.size).sum

theorem inputDenominator_pos (weights : List ℚ) : 0 < inputDenominator weights := by
  induction weights with
  | nil => simp [inputDenominator]
  | cons q rest ih => simpa only [inputDenominator, List.map_cons, List.prod_cons] using Nat.mul_pos q.den_pos ih

theorem inputDenominator_contains (weights : List ℚ) (q : ℚ) (member : q ∈ weights) :
    HasDenominator (inputDenominator weights) q := by
  unfold HasDenominator inputDenominator
  apply List.dvd_prod
  exact List.mem_map.mpr ⟨q, member, rfl⟩

theorem inputDenominator_bits (weights : List ℚ) :
    (inputDenominator weights).size ≤ denominatorBits weights + 1 := by
  have product_bound : inputDenominator weights ≤ 2 ^ denominatorBits weights := by
    induction weights with
    | nil => simp [inputDenominator, denominatorBits]
    | cons q rest ih =>
      simp only [inputDenominator, denominatorBits, List.map_cons, List.prod_cons, List.sum_cons, pow_add]
      exact Nat.mul_le_mul (Nat.lt_size_self _).le ih
  apply Nat.size_le.mpr
  apply product_bound.trans_lt
  rw [pow_succ]
  have := Nat.two_pow_pos (denominatorBits weights)
  omega

theorem denominatorBits_le (weights : List ℚ) (L : ℕ)
    (words : ∀ q ∈ weights, (Code.ofRat q).bits ≤ L) : denominatorBits weights ≤ weights.length * L := by
  unfold denominatorBits
  calc
    (weights.map fun q => q.den.size).sum ≤ (weights.map fun _ => L).sum := by
      apply List.sum_le_sum
      intro q member
      have bound := words q member
      simp only [Code.bits, Code.ofRat, Int.natAbs_natCast] at bound
      omega
    _ = _ := by simp [Nat.mul_comm]

theorem ratSum_input_words (values : List ℚ) (nonneg : ∀ q ∈ values, 0 ≤ q)
    (mass : values.sum ≤ 1) :
    WordsWithin (8 * denominatorBits values + 24) (ratSum values).events := by
  have words := ratSum_words (inputDenominator values) (inputDenominator_pos values) values
    (fun q member => inputDenominator_contains values q member) nonneg mass
  exact words.mono (by have := inputDenominator_bits values; omega)

end BuyAtBulk.Computation.Runtime.Original
