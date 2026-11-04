import BuyAtBulk.Computation.PolynomialLP.SearchPrecision

/-! Dyadic-grid invariant for actual bisection endpoints. Normalized rational
addition bounds are reset at every step using the common grid, preventing an
exponential recurrence in the number of queries. -/
namespace BuyAtBulk.PolynomialLP
open Computation.Rational

def OnGrid (U age : ℕ) (q : ℚ) : Prop :=
  ∃ z : ℤ, q=(z:ℚ)/(2:ℚ)^age ∧ z.natAbs≤2^(U+age)

theorem OnGrid.advance {U age : ℕ} {q : ℚ} (grid : OnGrid U age q) : OnGrid U (age+1) q := by
  obtain ⟨z,value,bound⟩ := grid
  refine ⟨2*z,?_,?_⟩
  · rw [value,pow_succ]
    push_cast
    field_simp
    <;> ring
  · simp only [Int.natAbs_mul,Int.natAbs_natCast]
    calc
      2*z.natAbs ≤ 2*2^(U+age) := Nat.mul_le_mul_left 2 bound
      _ = 2^(U+(age+1)) := by rw [← Nat.add_assoc,pow_succ]; omega

theorem OnGrid.midpoint {U age : ℕ} {q r : ℚ}
    (left : OnGrid U age q) (right : OnGrid U age r) : OnGrid U (age+1) ((q+r)/2) := by
  obtain ⟨z,qvalue,qbound⟩ := left
  obtain ⟨w,rvalue,rbound⟩ := right
  refine ⟨z+w,?_,?_⟩
  · rw [qvalue,rvalue,pow_succ]
    push_cast
    ring
  · calc
      (z+w).natAbs ≤ z.natAbs+w.natAbs := Int.natAbs_add_le _ _
      _ ≤ 2^(U+age)+2^(U+age) := Nat.add_le_add qbound rbound
      _ = 2^(U+(age+1)) := by rw [← Nat.add_assoc,pow_succ]; omega

theorem OnGrid.bits {U age : ℕ} {q : ℚ} (grid : OnGrid U age q) :
    (Code.ofRat q).bits ≤ 2*(U+age+1)+2 := by
  obtain ⟨z,value,bound⟩ := grid
  let raw : Code := ⟨z,(2:ℤ)^age,by positivity⟩
  have decoded : raw.value=q := by simpa [raw,Code.value] using value.symm
  rw [← decoded]
  apply (Code.normalized_bits_le raw).trans
  apply Code.bounded_bits
  constructor
  · exact bound.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))
  · change ((2:ℤ)^age).natAbs<2^(U+age+1)
    simp only [Int.natAbs_pow,Int.natAbs_natCast]
    exact Nat.pow_lt_pow_right (by decide) (by omega)

theorem searchBracket_grid (dimension L : ℕ) :
    OnGrid (L+dimension+2) 0 (searchBracket dimension L).lower ∧
    OnGrid (L+dimension+2) 0 (searchBracket dimension L).upper := by
  constructor
  · refine ⟨-((2:ℤ)^(L+dimension+2)),?_,?_⟩ <;>
      simp [searchBracket,searchMagnitude]
  · refine ⟨((2:ℤ)^(L+dimension+2)),?_,?_⟩ <;>
      simp [searchBracket,searchMagnitude]

theorem bisect_grid (decideBelow : ℚ → Bool) (rounds U age : ℕ) (bracket : Bracket)
    (lower : OnGrid U age bracket.lower) (upper : OnGrid U age bracket.upper) :
    OnGrid U (age+rounds) (bisect decideBelow rounds bracket).lower ∧
    OnGrid U (age+rounds) (bisect decideBelow rounds bracket).upper := by
  induction rounds generalizing age bracket with
  | zero => simpa [bisect] using And.intro lower upper
  | succ rounds ih =>
    have midpoint := lower.midpoint upper
    simp only [bisect]
    split
    · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (age+1) ⟨bracket.lower,(bracket.lower+bracket.upper)/2⟩ lower.advance midpoint
    · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (age+1) ⟨(bracket.lower+bracket.upper)/2,bracket.upper⟩ midpoint upper.advance

theorem bisect_search_bits (decideBelow : ℚ → Bool) (rounds dimension L : ℕ) :
    (Code.ofRat (bisect decideBelow rounds (searchBracket dimension L)).lower).bits ≤ 2*(L+dimension+rounds+3)+2 ∧
    (Code.ofRat (bisect decideBelow rounds (searchBracket dimension L)).upper).bits ≤ 2*(L+dimension+rounds+3)+2 := by
  have grid := bisect_grid decideBelow rounds (L+dimension+2) 0 _
    (searchBracket_grid dimension L).1 (searchBracket_grid dimension L).2
  constructor <;> first | simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using grid.1.bits | simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using grid.2.bits

end BuyAtBulk.PolynomialLP
