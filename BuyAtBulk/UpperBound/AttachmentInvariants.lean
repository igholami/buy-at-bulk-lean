import BuyAtBulk.UpperBound.AttachmentExecution
import Mathlib.Tactic.Linarith

/-! Structural invariants of the recursive source program: purchases persist,
each endpoint chain creates at most one record and at most one auxiliary edge,
and every returned/completed route is physically present in the final graph. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem append_toPath_bought {a b c : V} (first : G.Path a b) (second : G.Path b c)
    (bought : Finset V) (first_bought : first.val.support.toFinset ⊆ bought)
    (second_bought : second.val.support.toFinset ⊆ bought) :
    (first.val.append second.val).toPath.val.support.toFinset ⊆ bought := by
  intro x hx
  have hx' : x ∈ (first.val.append second.val).toPath.val.support := by
    simpa only [List.mem_toFinset] using hx
  have original := (first.val.append second.val).support_toPath_subset_support hx'
  cases (SimpleGraph.Walk.mem_support_append_iff first.val second.val).mp original with
  | inl left => exact first_bought (by simpa only [List.mem_toFinset] using left)
  | inr right => exact second_bought (by simpa only [List.mem_toFinset] using right)

def OutcomeBought {s t z u : V} (state : RoundingState G)
    (outcome : AttachmentOutcome G s t z u) : Prop :=
  match outcome with
  | .arm route => route.val.support.toFinset ⊆ state.bought
  | .completed route => route.val.support.toFinset ⊆ state.bought

namespace AttachmentExec

theorem bought_mono {buying physical : V → ℚ} {allowance cutoff ratio threshold : ℚ}
    {s t : V} {fuel : ℕ} {scale : ℚ} {z u : V} {inherited : G.Path z u}
    {before after : RoundingState G} {outcome : AttachmentOutcome G s t z u}
    (execution : AttachmentExec G buying physical allowance cutoff ratio threshold s t
      fuel scale z u inherited before after outcome) : before.bought ⊆ after.bought := by
  induction execution with
  | base => exact bought_subset_buyPath _ _ _
  | complete => exact bought_subset_buyPath _ _ _
  | birth => exact bought_subset_buyPath _ _ _
  | purchase => exact (bought_subset_buyPath _ _ _).trans (bought_subset_buyPath _ _ _)
  | reuse_arm _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | reuse_completed _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih

theorem centers_preserved {buying physical : V → ℚ} {allowance cutoff ratio threshold : ℚ}
    {s t : V} {fuel : ℕ} {scale : ℚ} {z u : V} {inherited : G.Path z u}
    {before after : RoundingState G} {outcome : AttachmentOutcome G s t z u}
    (execution : AttachmentExec G buying physical allowance cutoff ratio threshold s t
      fuel scale z u inherited before after outcome) : before.centers.Sublist after.centers := by
  induction execution with
  | base => exact List.Sublist.refl _
  | complete => exact List.Sublist.refl _
  | birth => exact List.sublist_cons_self _ _
  | purchase => exact List.Sublist.refl _
  | reuse_arm _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | reuse_completed _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih

theorem at_most_one_birth {buying physical : V → ℚ} {allowance cutoff ratio threshold : ℚ}
    {s t : V} {fuel : ℕ} {scale : ℚ} {z u : V} {inherited : G.Path z u}
    {before after : RoundingState G} {outcome : AttachmentOutcome G s t z u}
    (execution : AttachmentExec G buying physical allowance cutoff ratio threshold s t
      fuel scale z u inherited before after outcome) :
    after.centers.length ≤ before.centers.length + 1 := by
  induction execution with
  | base => simp [buyPath]
  | complete => simp [buyPath]
  | birth => simp [recordEdge, buyPath, recordBirth]
  | purchase => simp [recordEdge, buyPath]
  | reuse_arm _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | reuse_completed _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih

theorem at_most_one_edge {buying physical : V → ℚ} {allowance cutoff ratio threshold : ℚ}
    {s t : V} {fuel : ℕ} {scale : ℚ} {z u : V} {inherited : G.Path z u}
    {before after : RoundingState G} {outcome : AttachmentOutcome G s t z u}
    (execution : AttachmentExec G buying physical allowance cutoff ratio threshold s t
      fuel scale z u inherited before after outcome) :
    after.edges.length ≤ before.edges.length + 1 := by
  induction execution with
  | base => simp [buyPath]
  | complete => simp [buyPath]
  | birth => simp [recordEdge, buyPath, recordBirth]
  | purchase => simp [recordEdge, buyPath]
  | reuse_arm _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | reuse_completed _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih

theorem outcome_bought {buying physical : V → ℚ} {allowance cutoff ratio threshold : ℚ}
    {s t : V} {fuel : ℕ} {scale : ℚ} {z u : V} {inherited : G.Path z u}
    {before after : RoundingState G} {outcome : AttachmentOutcome G s t z u}
    (execution : AttachmentExec G buying physical allowance cutoff ratio threshold s t
      fuel scale z u inherited before after outcome) : OutcomeBought after outcome := by
  induction execution with
  | base => exact path_bought_buyPath _ _ _
  | complete => exact path_bought_buyPath _ _ _
  | birth => exact path_bought_buyPath _ _ _
  | purchase => exact (path_bought_buyPath _ _ _).trans (bought_subset_buyPath _ _ _)
  | reuse_arm inherited near bypass state final returned continues eligible shortest short
      bypass_bought bypass_short recursive ih =>
    exact append_toPath_bought returned bypass final.bought ih
      (bypass_bought.trans recursive.bought_mono)
  | reuse_completed _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih

end AttachmentExec
end BuyAtBulk.UpperBound
