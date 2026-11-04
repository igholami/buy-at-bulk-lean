import BuyAtBulk.Computation.Runtime.OptimizedParameters

namespace BuyAtBulk.Computation.Runtime.OptimizedParameters

theorem qSearch_count (target fuel current N : ℕ) (schedule : current+fuel≤N+1) :
    (qSearch target fuel current).events.length ≤ fuel*(2*N+4)+1 := by
  induction fuel generalizing current with
  | zero => simp[qSearch,emit]
  | succ k ih =>
    have recursive := ih (current+1) (by omega)
    simp only[qSearch,Traced.ite_events,emit_value]
    by_cases accepted : target≤(power current current).value
    all_goals simp only[accepted,decide_true,decide_false,Bool.false_eq_true,ite_true,ite_false,List.length_append,List.length_cons,List.length_nil,power_count,emit_length]
    all_goals nlinarith


def qCount (h : ℕ) := (2*h+1)*(4*h+8)+3

theorem q_count (h : ℕ) : (q h).events.length ≤ qCount h := by
  have result := qSearch_count (2*h) (2*h+1) 2 (2*h+2) (by omega)
  simp only[q,Traced.bind_events,Traced.bind_value,emit_length,emit_value,List.length_append]
  unfold qCount
  nlinarith


theorem squareSearch_count (target fuel current : ℕ) :
    (squareSearch target fuel current).events.length ≤ 4*fuel+1 := by
  induction fuel generalizing current with
  | zero => simp[squareSearch,emit]
  | succ k ih =>
    have recursive := ih (current+1)
    simp only[squareSearch,Traced.ite_events,emit_value]
    by_cases accepted : target≤current*current
    all_goals simp only[accepted,decide_true,decide_false,Bool.false_eq_true,ite_true,ite_false,List.length_append,List.length_cons,List.length_nil,emit_length]
    all_goals omega


theorem ceilSqrt_count (target : ℕ) : (ceilSqrt target).events.length ≤ 4*target+6 := by
  have result := squareSearch_count target (target+1) 0
  simp only[ceilSqrt,Traced.bind_events,Traced.bind_value,emit_value,emit_length,List.length_append]
  omega


def count (h : ℕ) := qCount h+8*h+18

theorem compute_count (h : ℕ) : (compute h).events.length ≤ count h := by
  have parameter := q_count h
  have root := ceilSqrt_count (q h).value
  have bound : (q h).value≤2*h+2 := by rw[q_value,←Parameters.q_eq];exact Parameters.q_bound h
  simp only[compute,Traced.bind_events,Traced.bind_value,emit_value,emit_length,List.length_append]
  unfold count
  omega

end BuyAtBulk.Computation.Runtime.OptimizedParameters
