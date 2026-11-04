import BuyAtBulk.Computation.Runtime.Rounding

namespace BuyAtBulk.Computation.Runtime.StoredRounding
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

def roundingCount (n h : ℕ) := (3*n+1)+freeCount n h+zeroCount n h+positiveCount n h+
  (h*(3*(n+1)+7)+1)+(2*h+1)+20

theorem run_count (buying physical opening : Vector ℚ n) (budget : ℚ) (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (ratio r : ℕ) (ratio_ge : 2 ≤ ratio) :
    (run input buying physical opening budget source target lengths ratio r ratio_ge).events.length ≤ roundingCount n h := by
  have free := freeRun_count input buying physical source target lengths
  have zero := zeroRun_count input buying physical opening budget source target lengths
  have zeroOutput := zeroRun_output_bound input buying physical opening budget source target lengths
  simp only[run]
  split
  · have flags := constantVector_count n false 1
    simp only[List.length_append,List.length_cons,List.length_nil,emit_length]
    unfold roundingCount
    omega
  · split
    · simp only[List.length_append,List.length_cons,List.length_nil,emit_length,zeroTest]
      unfold roundingCount
      omega
    · split
      · simp only[List.length_append,List.length_cons,List.length_nil,emit_length,zeroTest]
        unfold roundingCount
        omega
      · rename_i zeroAfter zeroEntries zeros
        simp only[zeros,resultLength] at zeroOutput
        have positive := positiveRun_count input buying physical opening budget source target lengths ratio r zeroAfter.bought ratio_ge
        split
        · simp only[List.length_append,List.length_cons,List.length_nil,emit_length,zeroTest]
          unfold roundingCount
          omega
        · rename_i after entries positives
          have projected := projectEntries_count input physical source target lengths zeroEntries
          have product := Nat.mul_le_mul_right (3*(n+1)+7) zeroOutput
          have projectionLength := (projectEntries_length input physical source target lengths zeroEntries).trans zeroOutput
          have copies := appendEntries_count input source target (projectEntries input physical source target lengths zeroEntries).value entries
          simp only[List.length_append,List.length_cons,List.length_nil,emit_length,zeroTest]
          unfold roundingCount
          omega

end BuyAtBulk.Computation.Runtime.StoredRounding
