import BuyAtBulk.Computation.PolynomialLP.BisectionBits
import BuyAtBulk.Computation.Runtime.Numerical

namespace BuyAtBulk.PolynomialLP
open Computation Computation.Runtime Computation.Rational

def bisectTrace (decideBelow : ℚ → Traced Bool) : ℕ → Bracket → Traced Bracket
  | 0, bracket => Traced.pure bracket
  | rounds+1, bracket => do
      let _ ← emit .scan [rounds.size] ()
      let lower ← emit .read [(Code.ofRat bracket.lower).bits] bracket.lower
      let upper ← emit .read [(Code.ofRat bracket.upper).bits] bracket.upper
      let sum ← ratAdd lower upper
      let midpoint ← ratDiv sum 2
      let yes ← decideBelow midpoint
      let yes ← branch yes
      let next := if yes then Bracket.mk lower midpoint else Bracket.mk midpoint upper
      let next ← emit .write [(Code.ofRat next.lower).bits,(Code.ofRat next.upper).bits] next
      bisectTrace decideBelow rounds next

@[simp] theorem bisectTrace_value (decideBelow : ℚ → Traced Bool) (rounds : ℕ) (bracket : Bracket) :
    (bisectTrace decideBelow rounds bracket).value = bisect (fun q => (decideBelow q).value) rounds bracket := by
  induction rounds generalizing bracket with
  | zero => rfl
  | succ rounds ih =>
    simp only [bisectTrace,Traced.bind_value,emit_value,ratAdd_value,ratDiv_value,branch,ih,bisect]
    split <;> simp_all

theorem bisectTrace_count (decideBelow : ℚ → Traced Bool) (rounds U age C : ℕ) (bracket : Bracket)
    (lower : OnGrid U age bracket.lower) (upper : OnGrid U age bracket.upper)
    (queries : ∀ t, t≤age+rounds → ∀ q, OnGrid U t q → (decideBelow q).events.length≤C) :
    (bisectTrace decideBelow rounds bracket).events.length≤rounds*(C+9) := by
  induction rounds generalizing age bracket with
  | zero => simp [bisectTrace,Traced.pure]
  | succ rounds ih =>
    have middle := lower.midpoint upper
    have query := queries (age+1) (by omega) _ middle
    have queries' : ∀ t, t≤age+1+rounds → ∀ q, OnGrid U t q → (decideBelow q).events.length≤C :=
      fun t ht q hq => queries t (by omega) q hq
    simp only [bisectTrace,Traced.bind_events,Traced.bind_value,emit_value,ratAdd_value,ratDiv_value,
      branch,List.length_append,emit_length,ratAdd_length,ratDiv_length]
    by_cases yes : (decideBelow ((bracket.lower+bracket.upper)/2)).value=true
    · simp only [yes,Bool.false_eq_true,ite_true,ite_false,Nat.add_mul,Nat.one_mul]
      have tail := ih (age+1) ⟨bracket.lower,(bracket.lower+bracket.upper)/2⟩ lower.advance middle queries'
      omega
    · simp only [yes,Bool.false_eq_true,ite_true,ite_false,Nat.add_mul,Nat.one_mul]
      have tail := ih (age+1) ⟨(bracket.lower+bracket.upper)/2,bracket.upper⟩ middle upper.advance queries'
      omega

theorem bisectTrace_words (decideBelow : ℚ → Traced Bool) (rounds U age K : ℕ) (bracket : Bracket)
    (lower : OnGrid U age bracket.lower) (upper : OnGrid U age bracket.upper)
    (capacity : 64*(U+age+rounds+2)+256≤K)
    (queries : ∀ t, t≤age+rounds → ∀ q, OnGrid U t q → WordsWithin K (decideBelow q).events) :
    WordsWithin K (bisectTrace decideBelow rounds bracket).events := by
  induction rounds generalizing age bracket with
  | zero => simp [bisectTrace,Traced.pure]
  | succ rounds ih =>
    have middle := lower.midpoint upper
    have lowerbits := lower.bits
    have upperbits := upper.bits
    have middlebits := middle.bits
    have query := queries (age+1) (by omega) _ middle
    have queries' : ∀ t, t≤age+1+rounds → ∀ q, OnGrid U t q → WordsWithin K (decideBelow q).events :=
      fun t ht q hq => queries t (by omega) q hq
    have capacity' : 64*(U+(age+1)+rounds+2)+256≤K := by omega
    have lowerK : (Code.ofRat bracket.lower).bits≤K := by omega
    have upperK : (Code.ofRat bracket.upper).bits≤K := by omega
    have middleK : (Code.ofRat ((bracket.lower+bracket.upper)/2)).bits≤K := by omega
    have sumBits := ratAdd_result_bits bracket.lower bracket.upper
    have two : (Code.ofRat (2:ℚ)).bits=5 := by decide
    have addWords : WordsWithin K (ratAdd bracket.lower bracket.upper).events :=
      by
        intro event member word present
        exact (ratAdd_words bracket.lower bracket.upper event member word present).trans (by omega)
    have divWords : WordsWithin K (ratDiv (bracket.lower+bracket.upper) 2).events :=
      by
        intro event member word present
        exact (ratDiv_words (bracket.lower+bracket.upper) 2 event member word present).trans (by omega)
    have counter : rounds.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
    have one : 1≤K := by omega
    simp only [bisectTrace,Traced.bind_events,Traced.bind_value,emit_value,ratAdd_value,ratDiv_value,branch,
      emit,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,
      forall_eq_or_imp,forall_eq,and_true]
    by_cases yes : (decideBelow ((bracket.lower+bracket.upper)/2)).value=true
    · simp only [yes,Bool.false_eq_true,ite_true,ite_false,Nat.add_mul,Nat.one_mul]
      have tail := ih (age+1) ⟨bracket.lower,(bracket.lower+bracket.upper)/2⟩ lower.advance middle capacity' queries'
      exact ⟨counter,lowerK,upperK,addWords,divWords,query,one,⟨lowerK,middleK⟩,tail⟩
    · simp only [yes,Bool.false_eq_true,ite_true,ite_false,Nat.add_mul,Nat.one_mul]
      have tail := ih (age+1) ⟨(bracket.lower+bracket.upper)/2,bracket.upper⟩ middle upper.advance capacity' queries'
      exact ⟨counter,lowerK,upperK,addWords,divWords,query,one,⟨middleK,upperK⟩,tail⟩

end BuyAtBulk.PolynomialLP
