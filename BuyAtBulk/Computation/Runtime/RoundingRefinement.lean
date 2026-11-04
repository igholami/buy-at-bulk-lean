import BuyAtBulk.Computation.Runtime.Rounding

set_option maxHeartbeats 2000000
namespace BuyAtBulk.Computation.Runtime.StoredRounding
open BuyAtBulk.UpperBound
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

theorem run_value (buying physical opening : Vector ℚ n) (budget : ℚ) (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (ratio r : ℕ) (ratio_ge : 2 ≤ ratio) :
    (run input buying physical opening budget source target lengths ratio r ratio_ge).value.map (decodeOutput input source target)=
      Rounding.run input.graph (Equiv.refl _) (fun v => buying[v.val]) (fun v => physical[v.val]) (fun v => opening[v.val]) budget
        (fun i => source[i.val]) (fun i => target[i.val]) (fun i => lengths[i.val]) ratio r := by
  simp only[run,Rounding.run,emit_value,zeroTest_value]
  by_cases empty : h=0
  · simp only[empty,decide_true,ite_true,Option.map_some,decodeOutput,constantFalse_set]
  · simp only[empty,decide_false,Bool.false_eq_true,ite_false]
    by_cases free : budget=0
    · simp only[free,decide_true,ite_true]
      exact freeRun_value input buying physical source target lengths
    · simp only[free,decide_false,Bool.false_eq_true,ite_false]
      have zeroEquation := zeroRun_value input buying physical opening budget source target lengths
      cases zeros : (zeroRun input buying physical opening budget source target lengths).value with
      | none =>
        simp only[zeros,decodeResult,Option.map_none] at zeroEquation
        simp only[zeros]
        rw[←zeroEquation]
        rfl
      | some result =>
        rcases result with ⟨zeroAfter,zeroEntries⟩
        simp only[zeros,decodeResult,Option.map_some] at zeroEquation
        simp only[zeros]
        rw[←zeroEquation]
        simp only[StoredState.decode]
        have positiveEquation := positiveRun_value input buying physical opening budget source target lengths
          ratio r zeroAfter.bought ratio_ge
        cases positives : (positiveRun input buying physical opening budget source target lengths
            ratio r zeroAfter.bought ratio_ge).value with
        | none =>
          simp only[positives,StoredBatch.decodeOption,Option.map_none] at positiveEquation
          simp only[positives]
          rw[←positiveEquation]
          rfl
        | some result =>
          rcases result with ⟨after,entries⟩
          simp only[positives,StoredBatch.decodeOption,Option.map_some] at positiveEquation
          simp only[positives]
          rw[←positiveEquation]
          simp only[Option.map_some,decodeOutput,projectEntries_value,appendEntries_value]
          rfl

end BuyAtBulk.Computation.Runtime.StoredRounding
