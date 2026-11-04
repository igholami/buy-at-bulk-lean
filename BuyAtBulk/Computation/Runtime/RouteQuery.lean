import BuyAtBulk.Computation.Runtime.Queries

/-! Path traversal and threshold filtering operate on the actual recovered
path. They do not reuse an uncharged semantic support sum. -/
namespace BuyAtBulk.Computation.Runtime.Queries
open BuyAtBulk.Computation.ShortestPath
open Rational
variable {n : ℕ} {G : SimpleGraph (Fin n)}

def cost (weights : Vector ℚ n) {u v : Fin n} : G.Walk u v → Traced ℚ
  | .nil =>
      let operand := readRat weights u
      ⟨operand.value, ⟨.branch, [1]⟩ :: operand.events⟩
  | .cons _ tail =>
      let operand := readRat weights u
      let recursive := cost weights tail
      let result := ratAdd operand.value recursive.value
      ⟨result.value, ⟨.branch, [1]⟩ :: operand.events ++ recursive.events ++ result.events⟩

@[simp] theorem cost_value (weights : Vector ℚ n) {u v : Fin n} (walk : G.Walk u v) :
    (cost weights walk).value = traversalCost G (fun x => weights[x.val]) walk := by
  induction walk with
  | nil => rfl
  | cons edge tail ih => simp only [cost, ratAdd_value, readRat, emit_value, ih, traversalCost_cons]

theorem cost_count (weights : Vector ℚ n) {u v : Fin n} (walk : G.Walk u v) :
    (cost weights walk).events.length ≤ 4 * (walk.length + 1) := by
  induction walk with
  | nil => simp [cost, readRat, emit]
  | cons edge tail ih =>
      simp only [cost, List.length_cons, List.length_append, ratAdd_length, readRat, emit_length,
        SimpleGraph.Walk.length_cons]
      omega

theorem cost_bits (weights : Vector ℚ n) {u v : Fin n} (walk : G.Walk u v)
    (R L : ℕ) (constant : 5 ≤ L) (bounded : walk.length ≤ R)
    (inputs : ∀ x : Fin n, (Code.ofRat weights[x.val]).bits + 1 ≤ L) :
    (Code.ofRat (cost weights walk).value).bits ≤ Runtime.ShortestPath.labelBudget R L := by
  have sum := HelperExpressions.sum_rat_bits (walk.support.map fun x => weights[x.val]) L constant (by
    intro q member
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp member
    exact inputs x)
  rw [← Runtime.ShortestPath.traversalCost_list, ← cost_value] at sum
  have length : (walk.support.map fun x => weights[x.val]).length ≤ R + 1 := by
    simp only [List.length_map, SimpleGraph.Walk.length_support]
    omega
  unfold Runtime.ShortestPath.labelBudget
  nlinarith

theorem cost_words (weights : Vector ℚ n) {u v : Fin n} (walk : G.Walk u v)
    (R L K : ℕ) (constant : 5 ≤ L) (bounded : walk.length ≤ R)
    (inputs : ∀ x : Fin n, (Code.ofRat weights[x.val]).bits + 1 ≤ L)
    (indices : n ≤ K) (budget : 2 * (L + Runtime.ShortestPath.labelBudget R L) + 9 ≤ K) :
    WordsWithin K (cost weights walk).events := by
  have one : 1 ≤ K := by omega
  have index_width (x : Fin n) : x.val.size ≤ K :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt x.isLt |>.trans indices)
  have input_width (x : Fin n) : (Code.ofRat weights[x.val]).bits ≤ L :=
    (Nat.le_add_right _ 1).trans (inputs x)
  revert bounded
  induction walk with
  | @nil a =>
      intro _
      have wi := (input_width a).trans (by omega : L ≤ K)
      simp [cost, readRat, emit, WordsWithin, one, index_width, wi]
  | @cons a b c edge tail ih =>
      intro bounded
      have tail_bound : tail.length ≤ R := by simpa using Nat.le_trans (Nat.le_succ tail.length) bounded
      have recursive := ih inputs input_width tail_bound
      have tail_bits := cost_bits weights tail R L constant tail_bound inputs
      have arithmetic : WordsWithin K (ratAdd weights[a.val] (cost weights tail).value).events := by
        intro event member word present
        exact (ratAdd_words _ _ event member word present).trans (by
          have wi := input_width a
          omega)
      have ai := index_width a
      have wi := (input_width a).trans (by omega : L ≤ K)
      simp only [cost, wordsWithin_append, wordsWithin_cons, wordsWithin_nil, readRat, emit,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
      aesop

variable (input : GraphEncoding n)

def shortRoute (weights : Vector ℚ n) (source target : Fin n) (threshold : ℚ) :
    Traced (Option (input.graph.Path source target)) :=
  let result := indexedPath input weights source target
  match result.value with
  | none => ⟨none, result.events ++ [⟨.branch, [1]⟩]⟩
  | some path =>
      let length := cost weights path.val
      let compared := ratLe length.value threshold
      ⟨if compared.value then some path else none,
        result.events ++ [⟨.branch, [1]⟩] ++ length.events ++
          [⟨.read, [(Code.ofRat threshold).bits]⟩] ++ compared.events ++ [⟨.branch, [1]⟩]⟩

theorem shortRoute_value (weights : Vector ℚ n) (source target : Fin n) (threshold : ℚ) :
    (shortRoute input weights source target threshold).value =
      Attachment.shortRoute input.graph (Equiv.refl _) (fun v => weights[v.val]) source target threshold := by
  unfold shortRoute Attachment.shortRoute
  rw [← indexedPath_value]
  cases returned : (indexedPath input weights source target).value with
  | none => simp [returned]
  | some path =>
      by_cases short : traversalCost input.graph (fun v => weights[v.val]) path.val ≤ threshold <;>
        simp [returned, cost_value, ratLe, emit, Attachment.pathCost, short]

theorem shortRoute_count (weights : Vector ℚ n) (source target : Fin n) (threshold : ℚ) :
    (shortRoute input weights source target threshold).events.length ≤
      (n + 1) ^ 2 * (10 * n ^ 2 + 30 * n + 36) + 3 * n ^ 2 + 8 * n + 14 := by
  have query := indexedPath_count input weights source target
  unfold shortRoute
  cases returned : (indexedPath input weights source target).value with
  | none =>
      simp only [returned, List.length_append, List.length_cons, List.length_nil]
      omega
  | some path =>
      have traversal := cost_count weights path.val
      have length : path.val.length < n := by simpa using path.property.length_lt
      simp only [returned, List.length_append, List.length_cons, List.length_nil, ratLe, emit]
      omega

theorem shortRoute_words (weights : Vector ℚ n) (source target : Fin n) (threshold : ℚ)
    (L M : ℕ) (constant : 5 ≤ L)
    (inputs : ∀ v : Fin n, (Code.ofRat weights[v.val]).bits + 1 ≤ L)
    (threshold_width : (Code.ofRat threshold).bits ≤ M) :
    WordsWithin (2 * (L + Runtime.ShortestPath.labelBudget n L) + 9 + n + n + M + 1)
      (shortRoute input weights source target threshold).events := by
  let K := 2 * (L + Runtime.ShortestPath.labelBudget n L) + 9 + n + n + M + 1
  have indices : n ≤ K := by dsimp [K]; omega
  have budget : 2 * (L + Runtime.ShortestPath.labelBudget n L) + 9 ≤ K := by dsimp [K]; omega
  have one : 1 ≤ K := by omega
  have query := (indexedPath_words input weights source target L constant inputs).mono
    (show 2 * (L + Runtime.ShortestPath.labelBudget n L) + 9 + n + n ≤ K by dsimp [K]; omega)
  unfold shortRoute
  cases returned : (indexedPath input weights source target).value with
  | none =>
      simpa only [returned, wordsWithin_append, wordsWithin_cons, wordsWithin_nil,
        List.mem_singleton, forall_eq, and_true] using And.intro query one
  | some path =>
      have length : path.val.length ≤ n := by simpa using Nat.le_of_lt path.property.length_lt
      have traversal := cost_words weights path.val n L K constant length inputs indices budget
      have length_width := cost_bits weights path.val n L constant length inputs
      have stored : (Code.ofRat threshold).bits ≤ K := threshold_width.trans (by dsimp [K]; omega)
      have result_width : (Code.ofRat (cost weights path.val).value).bits ≤ K := length_width.trans (by omega)
      simp only [returned, wordsWithin_append, wordsWithin_cons, wordsWithin_nil, ratLe, emit,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
      aesop

end BuyAtBulk.Computation.Runtime.Queries
