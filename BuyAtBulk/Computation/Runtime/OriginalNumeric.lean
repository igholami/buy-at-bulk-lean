import BuyAtBulk.Computation.Runtime.OriginalSum
import BuyAtBulk.Computation.HelperExpressions

/-! General nonnegative budget summation, with normalized and unreduced words
bounded polynomially by the actual number/width of stored rational inputs. -/
set_option maxHeartbeats 2400000
namespace BuyAtBulk.Computation.Runtime.Original
open Rational BuyAtBulk.Computation.FlowDecomposition

theorem size_mul_bound (a b : ℕ) : (a * b).size ≤ a.size + b.size + 1 := by
  have product : a * b ≤ 2 ^ (a.size + b.size) := by
    rw [pow_add]
    exact Nat.mul_le_mul (Nat.lt_size_self a).le (Nat.lt_size_self b).le
  apply Nat.size_le.mpr
  apply product.trans_lt
  rw [pow_succ]
  have := Nat.two_pow_pos (a.size + b.size)
  omega

theorem nonnegative_bits (q : ℚ) (D C : ℕ) (positive : 0 < D)
    (denominator : HasDenominator D q) (lower : 0 ≤ q) (upper : q ≤ C) :
    (Code.ofRat q).bits ≤ C.size + 2 * D.size + 3 := by
  have den_le : q.den ≤ D := Nat.le_of_dvd positive denominator
  have den_positive : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have quotient : (q.num : ℚ) / (q.den : ℚ) ≤ C := by simpa only [Rat.num_div_den] using upper
  have numeratorQ : (q.num : ℚ) ≤ (C : ℚ) * q.den := (div_le_iff₀ den_positive).mp quotient
  have num_nonneg : 0 ≤ q.num := Rat.num_nonneg.mpr lower
  have numeratorNat : q.num.natAbs ≤ C * q.den := by
    exact_mod_cast (show (q.num.natAbs : ℤ) ≤ (C : ℤ) * q.den by
      rw [Int.natAbs_of_nonneg num_nonneg]
      exact_mod_cast numeratorQ)
  have numeratorD : q.num.natAbs ≤ C * D := numeratorNat.trans (Nat.mul_le_mul_left C den_le)
  have num_bits := (Nat.size_le_size numeratorD).trans (size_mul_bound C D)
  have den_bits := Nat.size_le_size den_le
  simp only [Code.bits, Code.ofRat, Int.natAbs_natCast]
  omega

theorem ratSum_bounded_words (D C : ℕ) (positive : 0 < D) (values : List ℚ)
    (denominator : ∀ q ∈ values, HasDenominator D q)
    (nonneg : ∀ q ∈ values, 0 ≤ q) (mass : values.sum ≤ C) :
    WordsWithin (4 * C.size + 8 * D.size + 20) (ratSum values).events := by
  revert denominator nonneg mass
  induction values with
  | nil => intro _ _ _; simp [ratSum, WordsWithin, Code.bits, Code.ofRat]
  | cons q rest ih =>
    intro denominator nonneg mass
    have qlower := nonneg q (by simp)
    have taillower : 0 ≤ rest.sum := List.sum_nonneg (fun r mem => nonneg r (by simp [mem]))
    have qupper : q ≤ (C : ℚ) := by simp only [List.sum_cons] at mass; linarith
    have tailupper : rest.sum ≤ (C : ℚ) := by simp only [List.sum_cons] at mass; linarith
    have qbits := nonnegative_bits q D C positive (denominator q (by simp)) qlower qupper
    have tailden := sum_denominator D rest (fun r mem => denominator r (by simp [mem]))
    have tailbits := nonnegative_bits rest.sum D C positive tailden taillower tailupper
    have resultden := add_denominator D q rest.sum (denominator q (by simp)) tailden
    have resultbits := nonnegative_bits (q + rest.sum) D C positive resultden (add_nonneg qlower taillower)
      (by simpa only [List.sum_cons] using mass)
    have tailwords := ih (fun r mem => denominator r (by simp [mem]))
      (fun r mem => nonneg r (by simp [mem])) tailupper
    have addition : WordsWithin (4 * C.size + 8 * D.size + 20) (ratAdd q rest.sum).events := by
      intro event member word present
      exact (ratAdd_words q rest.sum event member word present).trans (by omega)
    have qbound : (Code.ofRat q).bits ≤ 4 * C.size + 8 * D.size + 20 := by omega
    have resultbound : (Code.ofRat (q + rest.sum)).bits ≤ 4 * C.size + 8 * D.size + 20 := by omega
    simp_all [ratSum, wordsWithin_append, wordsWithin_cons]

theorem nonnegative_value_bound (q : ℚ) (L : ℕ) (lower : 0 ≤ q) (bits : (Code.ofRat q).bits ≤ L) :
    q ≤ (2 ^ L : ℕ) := by
  have num_nonneg : 0 ≤ q.num := Rat.num_nonneg.mpr lower
  have numeratorQ : (0 : ℚ) ≤ q.num := by exact_mod_cast num_nonneg
  have denominatorQ : (1 : ℚ) ≤ q.den := by exact_mod_cast q.den_pos
  have quotient_le : q ≤ (q.num.natAbs : ℚ) := by
    calc
      q = (q.num : ℚ) / q.den := q.num_div_den.symm
      _ ≤ q.num := div_le_self numeratorQ denominatorQ
      _ = (q.num.natAbs : ℚ) := by
        have integer : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg num_nonneg
        have rational := congrArg (fun z : ℤ => (z : ℚ)) integer.symm
        simpa only [Int.cast_natCast] using rational
  have num_size : q.num.natAbs.size ≤ L := by
    simp only [Code.bits, Code.ofRat, Int.natAbs_natCast] at bits
    omega
  have numerator : q.num.natAbs ≤ 2 ^ L :=
    (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) num_size)
  exact quotient_le.trans (by exact_mod_cast numerator)

theorem nonnegative_mass_bound (values : List ℚ) (L : ℕ)
    (nonneg : ∀ q ∈ values, 0 ≤ q) (bits : ∀ q ∈ values, (Code.ofRat q).bits ≤ L) :
    values.sum ≤ (values.length * 2 ^ L : ℕ) := by
  calc
    values.sum = (values.map id).sum := by simp
    _ ≤ (values.map fun _ => ((2 ^ L : ℕ) : ℚ)).sum := by
      apply List.sum_le_sum
      intro q member
      exact nonnegative_value_bound q L (nonneg q member) (bits q member)
    _ = _ := by simp

theorem ratSum_polynomial_words (values : List ℚ) (L : ℕ)
    (nonneg : ∀ q ∈ values, 0 ≤ q) (bits : ∀ q ∈ values, (Code.ofRat q).bits ≤ L) :
    WordsWithin (8 * (values.length * L) + 4 * values.length + 4 * L + 36) (ratSum values).events := by
  have actual := ratSum_bounded_words (inputDenominator values) (values.length * 2 ^ L)
    (inputDenominator_pos values) values (fun q member => inputDenominator_contains values q member)
    nonneg (nonnegative_mass_bound values L nonneg bits)
  have den := inputDenominator_bits values
  have input_bits := denominatorBits_le values L bits
  have magnitude := size_mul_bound values.length (2 ^ L)
  rw [Nat.size_pow] at magnitude
  have list_size : values.length.size ≤ values.length := Nat.size_le.mpr Nat.lt_two_pow_self
  exact actual.mono (by omega)

/-- Signed normalized input sums also have polynomial words. The expression
bound is proof-only; this program executes only the normalized `ratSum` loop. -/
theorem ratSum_general_words (values : List ℚ) (L : ℕ) (constant : 5 ≤ L)
    (inputs : ∀ q ∈ values, (Code.ofRat q).bits + 1 ≤ L) :
    WordsWithin ((8 * values.length + 6) * L + 12) (ratSum values).events := by
  revert inputs
  induction values with
  | nil =>
    intro _
    simp [ratSum, WordsWithin, Code.bits, Code.ofRat]
  | cons q rest ih =>
    intro inputs
    have input := inputs q (by simp)
    have tail_inputs : ∀ r ∈ rest, (Code.ofRat r).bits + 1 ≤ L := fun r mem => inputs r (by simp [mem])
    have tailbits := HelperExpressions.sum_rat_bits rest L constant tail_inputs
    have resultbits := HelperExpressions.sum_rat_bits (q :: rest) L constant inputs
    have tailwords := (ih tail_inputs).mono (show (8 * rest.length + 6) * L + 12 ≤
        (8 * (q :: rest).length + 6) * L + 12 by simp only [List.length_cons]; nlinarith)
    have addition : WordsWithin ((8 * (q :: rest).length + 6) * L + 12) (ratAdd q rest.sum).events := by
      intro event member word present
      exact (ratAdd_words q rest.sum event member word present).trans (by simp only [List.length_cons]; nlinarith)
    have readbound : (Code.ofRat q).bits ≤ (8 * (q :: rest).length + 6) * L + 12 := by
      simp only [List.length_cons]
      nlinarith
    have writebound : (Code.ofRat (q + rest.sum)).bits ≤ (8 * (q :: rest).length + 6) * L + 12 := by
      simp only [List.sum_cons, List.length_cons] at resultbits ⊢
      nlinarith
    have one : 1 ≤ (8 * (q :: rest).length + 6) * L + 12 := by omega
    simp_all [ratSum, wordsWithin_append, wordsWithin_cons]

end BuyAtBulk.Computation.Runtime.Original
