import BuyAtBulk.Computation.Runtime.Primitive
import BuyAtBulk.Computation.HelperExpressions

/-! Width bounds for actual normalized rational operations and a fully
expanded doubling schedule for the helper's powers of two. -/
namespace BuyAtBulk.Computation.Runtime
open Rational

theorem wordBound_ratMul (a b : ℚ) :
    WordsWithin (2*((Code.ofRat a).bits+(Code.ofRat b).bits)+8) (ratMul a b).events := by
  have raw := Code.bounded_bits (Code.mul_bounded
    (Code.bounded_of_bits (Code.ofRat a)) (Code.bounded_of_bits (Code.ofRat b)))
  have normalized : (Code.ofRat (a*b)).bits ≤ ((Code.ofRat a).mul (Code.ofRat b)).bits := by
    simpa using Code.normalized_bits_le ((Code.ofRat a).mul (Code.ofRat b))
  change WordsWithin _ [⟨.ratMul, [(Code.ofRat a).bits, (Code.ofRat b).bits]⟩,
    ⟨.normalize, [((Code.ofRat a).mul (Code.ofRat b)).bits, (Code.ofRat (a*b)).bits]⟩]
  simp only [wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, and_true]
  constructor <;> constructor <;> omega

theorem wordBound_ratDiv (a b : ℚ) :
    WordsWithin (2*((Code.ofRat a).bits+(Code.ofRat b).bits)+8) (ratDiv a b).events := by
  have raw := Code.bounded_bits (Code.div_bounded
    (Code.bounded_of_bits (Code.ofRat a)) (Code.bounded_of_bits (Code.ofRat b)) (by omega))
  have normalized : (Code.ofRat (a/b)).bits ≤ ((Code.ofRat a).div (Code.ofRat b)).bits := by
    simpa using Code.normalized_bits_le ((Code.ofRat a).div (Code.ofRat b))
  change WordsWithin _ [⟨.ratDiv, [(Code.ofRat a).bits, (Code.ofRat b).bits]⟩,
    ⟨.normalize, [((Code.ofRat a).div (Code.ofRat b)).bits, (Code.ofRat (a/b)).bits]⟩]
  simp only [wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, and_true]
  constructor <;> constructor <;> omega

theorem normalized_add_bits (a b : ℚ) :
    (Code.ofRat (a+b)).bits ≤ 2*((Code.ofRat a).bits+(Code.ofRat b).bits)+8 := by
  have raw := Code.bounded_bits (Code.add_bounded
    (Code.bounded_of_bits (Code.ofRat a)) (Code.bounded_of_bits (Code.ofRat b)))
  have normalized : (Code.ofRat (a+b)).bits ≤ ((Code.ofRat a).add (Code.ofRat b)).bits := by
    simpa using Code.normalized_bits_le ((Code.ofRat a).add (Code.ofRat b))
  omega

theorem normalized_mul_bits (a b : ℚ) :
    (Code.ofRat (a*b)).bits ≤ 2*((Code.ofRat a).bits+(Code.ofRat b).bits)+8 := by
  have raw := Code.bounded_bits (Code.mul_bounded
    (Code.bounded_of_bits (Code.ofRat a)) (Code.bounded_of_bits (Code.ofRat b)))
  have normalized : (Code.ofRat (a*b)).bits ≤ ((Code.ofRat a).mul (Code.ofRat b)).bits := by
    simpa using Code.normalized_bits_le ((Code.ofRat a).mul (Code.ofRat b))
  omega

theorem normalized_div_bits (a b : ℚ) :
    (Code.ofRat (a/b)).bits ≤ 2*((Code.ofRat a).bits+(Code.ofRat b).bits)+8 := by
  have raw := Code.bounded_bits (Code.div_bounded
    (Code.bounded_of_bits (Code.ofRat a)) (Code.bounded_of_bits (Code.ofRat b)) (by omega))
  have normalized : (Code.ofRat (a/b)).bits ≤ ((Code.ofRat a).div (Code.ofRat b)).bits := by
    simpa using Code.normalized_bits_le ((Code.ofRat a).div (Code.ofRat b))
  omega

def powerTwo : ℕ → Traced ℕ
  | 0 => emit .write [1] 1
  | k+1 =>
      let previous := powerTwo k
      let result := 2*previous.value
      ⟨result, previous.events ++ [⟨.natMul, [2, previous.value.size, result.size]⟩,
        ⟨.write, [result.size]⟩]⟩

@[simp] theorem powerTwo_value (k : ℕ) : (powerTwo k).value = 2^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [powerTwo, ih, pow_succ']

theorem powerTwo_count (k : ℕ) : (powerTwo k).events.length = 2*k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [powerTwo, ih]; omega

theorem powerTwo_words (k : ℕ) : WordsWithin (k+2) (powerTwo k).events := by
  induction k with
  | zero => simp [powerTwo, emit, WordsWithin]
  | succ k ih =>
    have previous := ih.mono (show k+2 ≤ (k+1)+2 by omega)
    simp only [powerTwo, wordsWithin_append, powerTwo_value, ← pow_succ', Nat.size_pow]
    constructor
    · exact previous
    · simp only [wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, forall_eq, and_true]
      omega

theorem helperRepetitions_bound (h : ℕ) : Nat.clog 2 (8*h) ≤ 8*h :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)

theorem helperPower_runtime (h : ℕ) :
    (powerTwo (16*Nat.clog 2 (8*h))).value = 2^(16*Nat.clog 2 (8*h)) ∧
    (powerTwo (16*Nat.clog 2 (8*h))).events.length ≤ 256*h+1 ∧
    WordsWithin (128*h+2) (powerTwo (16*Nat.clog 2 (8*h))).events := by
  have exponent : 16*Nat.clog 2 (8*h) ≤ 128*h := by nlinarith [helperRepetitions_bound h]
  refine ⟨powerTwo_value _, ?_, ?_⟩
  · rw [powerTwo_count]; omega
  · exact (powerTwo_words _).mono (by omega)

/-- Ordinary multiplication loop, used to expand finite-grid powers as well
as helper powers. Its loop length is the actual exponent. -/
def power (base : ℕ) : ℕ → Traced ℕ
  | 0 => emit .write [1] 1
  | k+1 =>
      let previous := power base k
      let result := previous.value*base
      ⟨result, previous.events ++ [⟨.natMul, [previous.value.size,base.size,result.size]⟩,
        ⟨.write, [result.size]⟩]⟩

@[simp] theorem power_value (base k : ℕ) : (power base k).value = base^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [power, ih, pow_succ]

theorem power_count (base k : ℕ) : (power base k).events.length = 2*k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [power, ih]; omega

theorem power_size (base k : ℕ) : (base^k).size ≤ base.size*k+1 := by
  apply Nat.size_le.mpr
  have upper : base^k ≤ 2^(base.size*k) := by
    calc
      _ ≤ (2^base.size)^k := Nat.pow_le_pow_left (Nat.lt_size_self _).le _
      _ = _ := by rw [← pow_mul]
  have strict : (2 : ℕ)^(base.size*k) < 2^(base.size*k+1) := by
    rw [pow_succ]
    have positive : 0 < (2 : ℕ)^(base.size*k) := by positivity
    omega
  exact upper.trans_lt strict

theorem power_words (base k : ℕ) :
    WordsWithin ((base.size+1)*(k+1)+2) (power base k).events := by
  induction k with
  | zero => simp [power, emit, WordsWithin]
  | succ k ih =>
    have previous := ih.mono (show (base.size+1)*(k+1)+2 ≤ (base.size+1)*(k+1+1)+2 by nlinarith)
    have old_size := power_size base k
    have next_size := power_size base (k+1)
    simp only [power, wordsWithin_append, power_value, ← pow_succ]
    refine ⟨previous, ?_⟩
    simp only [wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, and_true]
    constructor
    · constructor
      · nlinarith
      · constructor <;> nlinarith
    · nlinarith

end BuyAtBulk.Computation.Runtime
