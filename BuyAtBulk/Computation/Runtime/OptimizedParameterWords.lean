import BuyAtBulk.Computation.Runtime.OptimizedParameterCost
import Mathlib.Tactic.GCongr

namespace BuyAtBulk.Computation.Runtime.OptimizedParameters

def searchWords (target N : ℕ) := (N+2)^2+target.size+N+10

theorem qSearch_words (target fuel current N : ℕ) (schedule : current+fuel≤N+1) :
    WordsWithin (searchWords target N) (qSearch target fuel current).events := by
  let K := searchWords target N
  have one : 1≤K := by dsimp[K,searchWords];omega
  have target_width : target.size≤K := by dsimp[K,searchWords];omega
  induction fuel generalizing current with
  | zero =>
    have width : current.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[K,searchWords];omega)
    simpa[qSearch,emit,wordsWithin_cons] using width
  | succ k ih =>
    have current_bound : current≤N := by omega
    have current_width : current.size≤N := (Nat.size_le.mpr Nat.lt_two_pow_self).trans current_bound
    have ci : current.size≤K := current_width.trans (by dsimp[K,searchWords];omega)
    have ni : (current+1).size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[K,searchWords];omega)
    have power_trace := (power_words current current).mono (show (current.size+1)*(current+1)+2≤K by
      have product := Nat.mul_le_mul (Nat.add_le_add_right current_width 1) (Nat.add_le_add_right current_bound 1)
      dsimp[K,searchWords]
      nlinarith)
    have power_width : (power current current).value.size≤K := by
      rw[power_value]
      have actual := power_size current current
      have product := Nat.mul_le_mul current_width current_bound
      dsimp[K,searchWords]
      nlinarith
    have recursive := ih (current+1) (by omega)
    simp only[qSearch,Traced.ite_events,emit_value]
    by_cases accepted : target≤(power current current).value
    all_goals simp only[accepted,decide_true,decide_false,Bool.false_eq_true,ite_true,ite_false,wordsWithin_append,emit,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
      or_false,forall_eq_or_imp,forall_eq,and_true]
    all_goals aesop


theorem squareSearch_words (target fuel current N : ℕ) (schedule : current+fuel≤N+1) :
    WordsWithin (searchWords target N) (squareSearch target fuel current).events := by
  let K := searchWords target N
  have one : 1≤K := by dsimp[K,searchWords];omega
  have target_width : target.size≤K := by dsimp[K,searchWords];omega
  induction fuel generalizing current with
  | zero =>
    have width : current.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[K,searchWords];omega)
    simpa[squareSearch,emit,wordsWithin_cons] using width
  | succ k ih =>
    have current_bound : current≤N := by omega
    have ci : current.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[K,searchWords];omega)
    have ni : (current+1).size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[K,searchWords];omega)
    have square_width : (current*current).size≤K := by
      have product := Nat.mul_le_mul current_bound current_bound
      exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[K,searchWords];nlinarith)
    have recursive := ih (current+1) (by omega)
    simp only[squareSearch,Traced.ite_events,emit_value]
    by_cases accepted : target≤current*current
    all_goals simp only[accepted,decide_true,decide_false,Bool.false_eq_true,ite_true,ite_false,wordsWithin_append,emit,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
      or_false,forall_eq_or_imp,forall_eq,and_true]
    all_goals aesop


def wordBudget (h : ℕ) := (2*h+4)^2+6*h+32


theorem q_words (h : ℕ) : WordsWithin (wordBudget h) (q h).events := by
  let K := wordBudget h
  have hi : h.size≤h := Nat.size_le.mpr Nat.lt_two_pow_self
  have ti : (2*h).size≤2*h := Nat.size_le.mpr Nat.lt_two_pow_self
  have fi : (2*h+1).size≤2*h+1 := Nat.size_le.mpr Nat.lt_two_pow_self
  have search := (qSearch_words (2*h) (2*h+1) 2 (2*h+2) (by omega)).mono (show searchWords (2*h) (2*h+2)≤K by
    dsimp[K,wordBudget,searchWords]
    nlinarith)
  have one : 1≤K := by dsimp[K,wordBudget];omega
  have two : 2≤K := by dsimp[K,wordBudget];omega
  simp only[q,Traced.bind_events,Traced.bind_value,emit_value,emit,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
    List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
  dsimp[K,wordBudget] at *
  aesop <;>omega


theorem ceilSqrt_words (target N : ℕ) (bounded : target≤N) :
    WordsWithin ((N+2)^2+3*N+16) (ceilSqrt target).events := by
  let K := (N+2)^2+3*N+16
  have ti : target.size≤N := (Nat.size_le.mpr Nat.lt_two_pow_self).trans bounded
  have fi : (target+1).size≤N+1 := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have search := (squareSearch_words target (target+1) 0 N (by omega)).mono (show searchWords target N≤K by dsimp[K,searchWords];omega)
  have one : 1≤K := by dsimp[K];omega
  simp only[ceilSqrt,Traced.bind_events,Traced.bind_value,emit_value,emit,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
    List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
  dsimp[K] at *
  aesop <;>omega


theorem compute_words (h : ℕ) : WordsWithin (wordBudget h) (compute h).events := by
  let K := wordBudget h
  have q_bound : (q h).value≤2*h+2 := by rw[q_value,←Parameters.q_eq];exact Parameters.q_bound h
  have root_bound : (ceilSqrt (q h).value).value≤2*h+2 := by
    rw[ceilSqrt_value]
    exact (ceilSqrt_le_self _).trans q_bound
  have parameter := q_words h
  have root := (ceilSqrt_words (q h).value (2*h+2) q_bound).mono (show ((2*h+2)+2)^2+3*(2*h+2)+16≤K by dsimp[K,wordBudget];nlinarith)
  have qi : (q h).value.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[K,wordBudget];omega)
  have ri : (ceilSqrt (q h).value).value.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[K,wordBudget];omega)
  have gi : (2*(q h).value).size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[K,wordBudget];omega)
  have four : 4≤K := by dsimp[K,wordBudget];omega
  have two : 2≤K := by omega
  have one : 1≤K := by omega
  have ratio_width : (if decide (8≤(ceilSqrt (q h).value).value) then (ceilSqrt (q h).value).value else 8).size≤K := by
    split_ifs
    · exact ri
    · have literal : (8 : ℕ).size=4 := by decide
      rw[literal]
      exact four
  simp only[compute,Traced.bind_events,Traced.bind_value,emit_value,emit,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
    List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
  aesop

end BuyAtBulk.Computation.Runtime.OptimizedParameters
