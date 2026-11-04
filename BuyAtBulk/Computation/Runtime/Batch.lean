import BuyAtBulk.Computation.Runtime.ServeWords
import BuyAtBulk.Computation.Runtime.ServeCost
import BuyAtBulk.Computation.Runtime.ServeRefinement
import BuyAtBulk.Computation.Batch.Algorithm

/-! Actual stored batch program. The original commodity count is fixed across
all recursive calls; returned paths retain their original request index. -/
namespace BuyAtBulk.Computation.Runtime.StoredBatch
open BuyAtBulk.UpperBound
open Rational
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

abbrev Entry (source target : Vector (Fin n) h) := Σ i : Fin h, input.graph.Path source[i.val] target[i.val]

def run (buying physical : Vector ℚ n) (budget : ℚ) (ratio : ℕ) (thresholdFactor : ℚ)
    (source target : Vector (Fin n) h) (allowance : Vector ℚ h) :
    List (Fin h) → StoredState.State input.graph → Traced (Option (StoredState.State input.graph × List (Entry input source target)))
  | [], before => ⟨some (before, []), [⟨.branch, [1]⟩, ⟨.cons, [1]⟩]⟩
  | i :: rest, before =>
    let threshold := ratMul thresholdFactor allowance[i.val]
    let served : Traced (Option (StoredState.State input.graph × input.graph.Path source[i.val] target[i.val])) := StoredServe.run input buying physical budget allowance[i.val] h ratio threshold.value source[i.val] target[i.val] before
    let headEvents : List Event := [⟨Operation.scan, [i.val.size]⟩, ⟨.read, [source[i.val].val.size]⟩,
      ⟨.read, [target[i.val].val.size]⟩, ⟨.read, [(Code.ofRat allowance[i.val]).bits]⟩,
      ⟨.read, [(Code.ofRat thresholdFactor).bits]⟩] ++ threshold.events ++ served.events ++ [(⟨.branch, [1]⟩ : Event)]
    show Traced (Option (StoredState.State input.graph × List (Entry input source target))) from
    match served.value with
    | none => ⟨none, headEvents⟩
    | some (middle, route) =>
      let next : Traced (Option (StoredState.State input.graph × List (Entry input source target))) := run buying physical budget ratio thresholdFactor source target allowance rest middle
      show Traced (Option (StoredState.State input.graph × List (Entry input source target))) from
      match next.value with
      | none => ⟨none, headEvents ++ next.events ++ [(⟨.branch, [1]⟩ : Event)]⟩
      | some (after, entries) =>
          ⟨some (after, ⟨i, route⟩ :: entries), headEvents ++ next.events ++ [(⟨.branch, [1]⟩ : Event), ⟨.cons, [i.val.size]⟩]⟩

def decodeOption (source target : Vector (Fin n) h) :
    Option (StoredState.State input.graph × List (Entry input source target)) →
      Option (RoundingState input.graph × List (Entry input source target)) :=
  Option.map fun result => (StoredState.decode input.graph result.1, result.2)

theorem run_value (buying physical : Vector ℚ n) (budget : ℚ) (ratio : ℕ) (thresholdFactor : ℚ)
    (source target : Vector (Fin n) h) (allowance : Vector ℚ h) (order : List (Fin h))
    (before : StoredState.State input.graph) (ratio_ge : 2 ≤ ratio) :
    decodeOption input source target (run input buying physical budget ratio thresholdFactor source target allowance order before).value =
      Computation.Batch.run input.graph (Equiv.refl _) (fun v => buying[v.val]) (fun v => physical[v.val]) budget ratio thresholdFactor
        (fun i => source[i.val]) (fun i => target[i.val]) (fun i => allowance[i.val]) order (StoredState.decode input.graph before) := by
  induction order generalizing before with
  | nil => rfl
  | cons i rest ih =>
      have served := StoredServe.run_value input buying physical budget allowance[i.val] h ratio (thresholdFactor * allowance[i.val])
        source[i.val] target[i.val] before ratio_ge
      simp only [run, ratMul_value]
      cases returned : (StoredServe.run input buying physical budget allowance[i.val] h ratio (thresholdFactor * allowance[i.val]) source[i.val] target[i.val] before).value with
      | none =>
          simp only [returned, StoredServe.decodeOption, Option.map_none] at served
          simp only [Computation.Batch.run, ← served, decodeOption, Option.map_none]
      | some result =>
          rcases result with ⟨middle, route⟩
          simp only [returned, StoredServe.decodeOption, Option.map_some, StoredServe.decodeRoute] at served
          simp only [Computation.Batch.run, ← served]
          have next := ih middle
          cases later : (run input buying physical budget ratio thresholdFactor source target allowance rest middle).value with
          | none =>
              simp only [later, decodeOption, Option.map_none] at next ⊢
              rw [← next]
          | some result =>
              rcases result with ⟨after, entries⟩
              simp only [later, decodeOption, Option.map_some] at next ⊢
              rw [← next]

/-- Successful stored outputs preserve a predicate without asserting success. -/
def StateProperty (source target : Vector (Fin n) h) (property : StoredState.State input.graph → Prop) :
    Option (StoredState.State input.graph × List (Entry input source target)) → Prop
  | none => True
  | some result => property result.1

theorem run_growth (buying physical : Vector ℚ n) (budget : ℚ) (ratio : ℕ) (thresholdFactor : ℚ)
    (source target : Vector (Fin n) h) (allowance : Vector ℚ h) (order : List (Fin h))
    (before : StoredState.State input.graph) :
    StateProperty input source target (StoredServe.Growth input before (4*order.length) (2*order.length))
      (run input buying physical budget ratio thresholdFactor source target allowance order before).value := by
  induction order generalizing before with
  | nil => simp [run, StateProperty, StoredServe.Growth]
  | cons i rest ih =>
      have grown := StoredServe.run_growth input buying physical budget allowance[i.val] h ratio (ratMul thresholdFactor allowance[i.val]).value
        source[i.val] target[i.val] before
      simp only [run]
      split
      · trivial
      · rename_i middle route served
        simp only [served, StoredServe.StateProperty, StoredServe.Growth] at grown
        have next := ih middle
        split
        · trivial
        · rename_i after entries later
          simp only [later, StateProperty, StoredServe.Growth] at next
          simp only [StateProperty, StoredServe.Growth, List.length_cons]
          constructor <;> omega

theorem serveBudget_mono {m M : ℕ} (bounded : m ≤ M) :
    StoredServe.serveBudget n h m ≤ StoredServe.serveBudget n h M := by
  have reuse := StoredServe.reuseBudget_mono (n:=n) h (Nat.add_le_add_right bounded 2)
  have mul := Nat.mul_le_mul_right (AttachmentQueries.routeBudget n+10) (Nat.add_le_add_right bounded 1)
  unfold StoredServe.serveBudget StoredServe.mainPhaseBudget
  omega

def countBudget (n h m k : ℕ) := k*(StoredServe.serveBudget n h (m+4*k)+10)+2

theorem run_count (buying physical : Vector ℚ n) (budget : ℚ) (ratio : ℕ) (thresholdFactor : ℚ)
    (source target : Vector (Fin n) h) (allowance : Vector ℚ h) (order : List (Fin h))
    (before : StoredState.State input.graph) (ratio_ge : 2 ≤ ratio) :
    (run input buying physical budget ratio thresholdFactor source target allowance order before).events.length ≤
      countBudget n h before.centers.length order.length := by
  suffices general : ∀ (order : List (Fin h)) (before : StoredState.State input.graph) (M : ℕ),
      before.centers.length+4*order.length ≤ M →
      (run input buying physical budget ratio thresholdFactor source target allowance order before).events.length ≤
        order.length*(StoredServe.serveBudget n h M+10)+2 by
    exact general order before _ (by omega)
  intro order
  induction order with
  | nil => intro before M bounded; simp [run]
  | cons i rest ih =>
      intro before M bounded
      have served_count := (StoredServe.run_count input buying physical budget allowance[i.val] h ratio (ratMul thresholdFactor allowance[i.val]).value
        source[i.val] target[i.val] before ratio_ge).trans (serveBudget_mono (by omega : before.centers.length ≤ M))
      have grown := StoredServe.run_growth input buying physical budget allowance[i.val] h ratio (ratMul thresholdFactor allowance[i.val]).value
        source[i.val] target[i.val] before
      simp only [run]
      split
      · simp only [List.length_append, List.length_cons, List.length_nil, ratMul_length]
        simp only [List.length_cons] at bounded ⊢
        nlinarith
      · rename_i middle route returned
        simp only [returned, StoredServe.StateProperty, StoredServe.Growth] at grown
        have next := ih middle M (by simp only [List.length_cons] at bounded; omega)
        split <;> simp only [List.length_append, List.length_cons, List.length_nil, ratMul_length] <;> nlinarith

end BuyAtBulk.Computation.Runtime.StoredBatch
