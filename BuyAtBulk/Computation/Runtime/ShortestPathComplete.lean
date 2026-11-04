import BuyAtBulk.Computation.Runtime.Recovery
import BuyAtBulk.Computation.Runtime.Paths

/-! Full computed shortest-path query, including recovery table recomputation
and actual cycle erasure. This is a rational word-operation model; normalizing
arithmetic is atomic with recorded raw and normalized operand widths. -/
namespace BuyAtBulk.Computation.Runtime.ShortestPath
open BuyAtBulk.Computation.ShortestPath
open Rational
variable {n : ℕ}

def path (input : GraphEncoding n) (weights : Vector ℚ n) (source target : Fin n) :
    Traced (Option (input.graph.Path source target)) :=
  let recovery := recover input weights target n source
  match recovery.value with
  | none => ⟨none, recovery.events ++ [⟨.branch, [1]⟩]⟩
  | some walk =>
      let result := Paths.toPath walk
      ⟨some result.value, recovery.events ++ [⟨.branch, [1]⟩] ++ result.events⟩

theorem path_value (input : GraphEncoding n) (weights : Vector ℚ n) (source target : Fin n) :
    (path input weights source target).value = input.path weights source target := by
  unfold path GraphEncoding.path BuyAtBulk.Computation.ShortestPath.shortestPath
  rw [← recover_value]
  cases returned : (recover input weights target n source).value <;> simp [returned, Paths.toPath_value]

theorem path_count (input : GraphEncoding n) (weights : Vector ℚ n) (source target : Fin n) :
    (path input weights source target).events.length ≤
      (n + 1) ^ 2 * (10 * n ^ 2 + 30 * n + 36) + 1 := by
  have recovery := recover_count input weights target n source
  unfold path
  cases returned : (recover input weights target n source).value with
  | none =>
      simp only [returned, List.length_append, List.length_cons, List.length_nil]
      nlinarith
  | some walk =>
      have actual : BuyAtBulk.Computation.ShortestPath.recover input.graph
          (fun v => weights[v.val]) target n source = some walk :=
        (recover_value input weights target n source).symm.trans returned
      have length := (recover_valid input.graph (fun v => weights[v.val]) target n source walk actual).2
      have erased := Paths.toPath_count walk
      simp only [returned, List.length_append, List.length_cons, List.length_nil]
      nlinarith

theorem path_words (input : GraphEncoding n) (weights : Vector ℚ n) (source target : Fin n)
    (L : ℕ) (constant : 5 ≤ L)
    (inputs : ∀ v : Fin n, (Code.ofRat weights[v.val]).bits + 1 ≤ L) :
    WordsWithin (2 * (L + labelBudget n L) + 9 + n + n)
      (path input weights source target).events := by
  have recovery := recover_words input weights target n L constant inputs source
  have one : 1 ≤ 2 * (L + labelBudget n L) + 9 + n + n := by omega
  unfold path
  cases returned : (recover input weights target n source).value with
  | none =>
      simpa only [returned, wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_singleton,
        forall_eq, and_true] using And.intro recovery one
  | some walk =>
      have erased := Paths.toPath_words walk (2 * (L + labelBudget n L) + 9 + n + n) (by omega) one
      simpa only [returned, wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_singleton,
        forall_eq, and_true] using And.intro (And.intro recovery one) erased

/-- The actual graph-input query has the existing exact output, polynomial
primitive-event count and polynomial maximum rational/index word width. -/
theorem path_runtime (input : GraphEncoding n) (weights : Vector ℚ n) (source target : Fin n)
    (L : ℕ) (constant : 5 ≤ L)
    (inputs : ∀ v : Fin n, (Code.ofRat weights[v.val]).bits + 1 ≤ L) :
    (path input weights source target).value = input.path weights source target ∧
    (path input weights source target).events.length ≤
      (n + 1) ^ 2 * (10 * n ^ 2 + 30 * n + 36) + 1 ∧
    WordsWithin (2 * (L + labelBudget n L) + 9 + n + n)
      (path input weights source target).events :=
  ⟨path_value input weights source target, path_count input weights source target,
    path_words input weights source target L constant inputs⟩

end BuyAtBulk.Computation.Runtime.ShortestPath
