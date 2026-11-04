import BuyAtBulk.UpperBound.ServeInvariants

/-! Batch execution on a subset of the original h indexed requests. The same
h remains the grid/cutoff normalization even when only a subset is served.
Nondecreasing allowances and distinct indices specify the source run order. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

inductive RunExec {h : ℕ} (buying physical : V → ℚ) (budget : ℚ) (ratio : ℕ)
    (thresholdFactor : ℚ) (source target : Fin h → V) (allowance : Fin h → ℚ) :
    List (Fin h) → RoundingState G → RoundingState G → Prop where
  | nil (state : RoundingState G) : RunExec buying physical budget ratio thresholdFactor source target allowance [] state state
  | cons (i : Fin h) (order : List (Fin h)) (before middle after : RoundingState G)
      (reachable : Nonempty (G.Path (source i) (target i))) (route : G.Path (source i) (target i))
      (served : ServeExec G buying physical budget (allowance i) h ratio (thresholdFactor * allowance i)
        (source i) (target i) reachable before middle route)
      (rest : RunExec buying physical budget ratio thresholdFactor source target allowance order middle after) :
      RunExec buying physical budget ratio thresholdFactor source target allowance (i :: order) before after

def OrderedRun {h : ℕ} (buying physical : V → ℚ) (budget : ℚ) (ratio : ℕ)
    (thresholdFactor : ℚ) (source target : Fin h → V) (allowance : Fin h → ℚ)
    (order : List (Fin h)) (before after : RoundingState G) : Prop :=
  order.Nodup ∧ order.Pairwise (fun i j => allowance i ≤ allowance j) ∧
    RunExec G buying physical budget ratio thresholdFactor source target allowance order before after

namespace RunExec

theorem bought_mono {h : ℕ} {buying physical : V → ℚ} {budget : ℚ} {ratio : ℕ}
    {thresholdFactor : ℚ} {source target : Fin h → V} {allowance : Fin h → ℚ}
    {order : List (Fin h)} {before after : RoundingState G}
    (execution : RunExec G buying physical budget ratio thresholdFactor source target allowance order before after) :
    before.bought ⊆ after.bought := by
  induction execution with
  | nil => exact Finset.Subset.refl _
  | cons i order before middle after reachable route served rest ih => exact served.bought_mono.trans ih

theorem record_count {h : ℕ} {buying physical : V → ℚ} {budget : ℚ} {ratio : ℕ}
    {thresholdFactor : ℚ} {source target : Fin h → V} {allowance : Fin h → ℚ}
    {order : List (Fin h)} {before after : RoundingState G}
    (execution : RunExec G buying physical budget ratio thresholdFactor source target allowance order before after) :
    after.centers.length ≤ before.centers.length + 2 * order.length := by
  induction execution with
  | nil => simp
  | cons i order before middle after reachable route served rest ih =>
    have served_count := served.at_most_two_births
    simp only [List.length_cons]
    omega

theorem centers_count_le_two_h {h : ℕ} {buying physical : V → ℚ} {budget : ℚ} {ratio : ℕ}
    {thresholdFactor : ℚ} {source target : Fin h → V} {allowance : Fin h → ℚ}
    {order : List (Fin h)} {before after : RoundingState G}
    (execution : RunExec G buying physical budget ratio thresholdFactor source target allowance order before after)
    (initial_empty : before.centers = []) (nodup : order.Nodup) : after.centers.length ≤ 2 * h := by
  have count := execution.record_count
  rw [initial_empty] at count
  have requests_le : order.length ≤ h := by
    have cardinality := Finset.card_le_univ order.toFinset
    rw [List.toFinset_card_of_nodup nodup] at cardinality
    simpa using cardinality
  simp only [List.length_nil, zero_add] at count
  exact count.trans (Nat.mul_le_mul_left 2 requests_le)

end RunExec
end BuyAtBulk.UpperBound
