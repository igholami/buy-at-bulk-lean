import BuyAtBulk.Computation.Runtime.Core

set_option maxHeartbeats 1200000
namespace BuyAtBulk.Computation.Runtime.StoredBatch
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

theorem run_length (buying physical : Vector ℚ n) (budget : ℚ) (ratio : ℕ) (threshold : ℚ)
    (source target : Vector (Fin n) h) (allowance : Vector ℚ h) (order : List (Fin h)) (before after : StoredState.State input.graph)
    (entries : List (Entry input source target))
    (returned : (run input buying physical budget ratio threshold source target allowance order before).value=some (after,entries)) :
    entries.length ≤ order.length := by
  induction order generalizing before after entries with
  | nil =>
    simp only[run,emit_value,Option.some.injEq,Prod.mk.injEq] at returned
    rw[←returned.2]
    simp
  | cons i rest ih =>
    simp only[run] at returned
    split at returned
    · contradiction
    · rename_i middle route served
      split at returned
      · contradiction
      · rename_i final routes later
        have same : final=after ∧ (⟨i,route⟩ : Entry input source target)::routes=entries := Prod.mk.inj (Option.some.inj returned)
        have bound := ih middle final routes later
        rw[←same.2]
        simp only[List.length_cons]
        omega

end BuyAtBulk.Computation.Runtime.StoredBatch

namespace BuyAtBulk.Computation.Runtime.StoredCore
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

theorem execute_output_length (buying physical : Vector ℚ n) (budget : ℚ) (allowance : Vector ℚ h)
    (source target : Vector (Fin n) h) (active : Vector Bool h) (ratio r : ℕ) (seed : Vector Bool n) (nodes : List (Fin n))
    (after : StoredState.State input.graph) (entries : List (StoredBatch.Entry input source target))
    (returned : (execute input buying physical budget allowance source target active ratio r seed nodes).value=some (after,entries)) :
    entries.length ≤ h := by
  have bound := StoredBatch.run_length input buying physical budget ratio (thresholdFactor r).value source target allowance
    (requestOrder active allowance).value (initialState input buying seed nodes).value after entries returned
  exact bound.trans (requestOrder_length active allowance)

theorem run_output_length (buying physical opening : Vector ℚ n) (budget : ℚ) (allowance : Vector ℚ h)
    (source target : Vector (Fin n) h) (active : Vector Bool h) (ratio r : ℕ) (seed : Vector Bool n) (ratio_ge : 2 ≤ ratio)
    (after : StoredState.State input.graph) (entries : List (StoredBatch.Entry input source target))
    (returned : (run input buying physical opening budget allowance source target active ratio r seed ratio_ge).value=some (after,entries)) :
    entries.length ≤ h := by
  simp only[run,Traced.bind_value] at returned
  exact execute_output_length input buying physical budget allowance source target active ratio r seed _ after entries returned

end BuyAtBulk.Computation.Runtime.StoredCore
