import BuyAtBulk.Computation.Runtime.ShortestPath

/-! Actual predecessor scans, including early stopping. Each tested
predecessor produces its own arithmetic/read/control events. -/
namespace BuyAtBulk.Computation.Runtime.ShortestPath
open BuyAtBulk.Computation.ShortestPath
open Rational
variable {n : ℕ}

def edgeChoiceList (input : GraphEncoding n) (weights : Vector ℚ n)
    (old : Vector (WithTop ℚ) n) (v : Fin n) (value : WithTop ℚ) :
    List (Fin n) → Traced (Option (Fin n))
  | [] => ⟨none, [⟨.branch, [1]⟩]⟩
  | u :: rest =>
      let control : List Event := [⟨.scan, [u.val.size]⟩,
        ⟨.read, [v.val.size, u.val.size, 1]⟩, ⟨.branch, [1]⟩]
      if input.adjacency[v.val][u.val] then
        let operand := read old u
        let sum := addition weights[v.val] operand.value
        let tested : List Event := control ++
          [⟨.read, [v.val.size, (Code.ofRat weights[v.val]).bits]⟩] ++ operand.events ++ sum.events ++
          [⟨.ratCompare, [width sum.value, width value]⟩, ⟨.branch, [1]⟩]
        if sum.value = value then ⟨some u, tested⟩ else
          let recursive := edgeChoiceList input weights old v value rest
          ⟨recursive.value, tested ++ recursive.events⟩
      else
        let recursive := edgeChoiceList input weights old v value rest
        ⟨recursive.value, control ++ recursive.events⟩

theorem edgeChoiceList_value (input : GraphEncoding n) (weights : Vector ℚ n)
    (old : Vector (WithTop ℚ) n) (v : Fin n) (value : WithTop ℚ) (vertices : List (Fin n)) :
    (edgeChoiceList input weights old v value vertices).value =
      vertices.find? (fun u => decide (input.graph.Adj v u ∧
        (weights[v.val] : WithTop ℚ) + old[u.val] = value)) := by
  induction vertices with
  | nil => rfl
  | cons u rest ih =>
      simp only [edgeChoiceList]
      cases adjacent : input.adjacency[v.val][u.val] <;>
        simp [adjacent, read, addition_value, List.find?, GraphEncoding.graph, ih]
      split_ifs <;> simp_all

theorem edgeChoiceList_count (input : GraphEncoding n) (weights : Vector ℚ n)
    (old : Vector (WithTop ℚ) n) (v : Fin n) (value : WithTop ℚ) (vertices : List (Fin n)) :
    (edgeChoiceList input weights old v value vertices).events.length ≤ 10 * vertices.length + 1 := by
  induction vertices with
  | nil => simp [edgeChoiceList]
  | cons u rest ih =>
      have bound := addition_count weights[v.val] old[u.val]
      simp only [edgeChoiceList]
      split
      · split <;> simp only [List.length_append, List.length_cons, List.length_nil, read, emit]
        · omega
        · omega
      · simp only [List.length_append, List.length_cons, List.length_nil]
        omega

def edgeChoice (input : GraphEncoding n) (weights : Vector ℚ n)
    (old : Vector (WithTop ℚ) n) (v : Fin n) (value : WithTop ℚ) : Traced (Option (Fin n)) :=
  let vertices := indexList n
  let result := edgeChoiceList input weights old v value vertices.value
  ⟨result.value, vertices.events ++ result.events⟩

@[simp] theorem edgeChoice_value (input : GraphEncoding n) (weights : Vector ℚ n)
    (old : Vector (WithTop ℚ) n) (v : Fin n) (value : WithTop ℚ) :
    (edgeChoice input weights old v value).value =
      BuyAtBulk.Computation.ShortestPath.edgeChoice input.graph (fun x => weights[x.val]) old v value :=
  by simpa only [edgeChoice, indexList_value, BuyAtBulk.Computation.ShortestPath.edgeChoice] using
    edgeChoiceList_value input weights old v value (List.finRange n)

theorem edgeChoice_count (input : GraphEncoding n) (weights : Vector ℚ n)
    (old : Vector (WithTop ℚ) n) (v : Fin n) (value : WithTop ℚ) :
    (edgeChoice input weights old v value).events.length ≤ 13 * n + 1 := by
  have bound := edgeChoiceList_count input weights old v value (List.finRange n)
  simp only [edgeChoice, indexList_value, List.length_append, indexList_count]
  simp only [List.length_finRange] at bound
  omega

def recover (input : GraphEncoding n) (weights : Vector ℚ n) (target : Fin n) :
    (rounds : ℕ) → (v : Fin n) → Traced (Option (input.graph.Walk v target))
  | 0, v =>
      ⟨if same : v = target then some ((SimpleGraph.Walk.nil : input.graph.Walk v v).copy rfl same) else none,
        [⟨.recurse, [1]⟩, ⟨.branch, [v.val.size, target.val.size]⟩, ⟨.cons, [1]⟩]⟩
  | rounds + 1, v =>
      let old := iterate input weights target rounds
      let next := step input weights old.value
      let control := [⟨Operation.recurse, [rounds.size]⟩] ++ old.events ++ next.events ++
        (read old.value v).events ++ (read next.value v).events ++
        [⟨.ratCompare, [width old.value[v.val], width next.value[v.val]]⟩, ⟨.branch, [1]⟩]
      if old.value[v.val] = next.value[v.val] then
        let recursive := recover input weights target rounds v
        ⟨recursive.value, control ++ recursive.events⟩
      else
        let choice := edgeChoice input weights old.value v next.value[v.val]
        match found : choice.value with
        | none => ⟨none, control ++ choice.events ++ [⟨.branch, [1]⟩]⟩
        | some u =>
            let recursive := recover input weights target rounds u
            let edge := (edgeChoice_spec input.graph (fun x => weights[x.val]) old.value v u next.value[v.val]
              ((edgeChoice_value input weights old.value v next.value[v.val]).symm.trans found)).1
            ⟨recursive.value.map (fun walk => .cons edge walk),
              control ++ choice.events ++ [⟨.branch, [1]⟩] ++ recursive.events ++
                [⟨.branch, [1]⟩, ⟨.cons, [u.val.size, v.val.size]⟩]⟩

theorem recover_value (input : GraphEncoding n) (weights : Vector ℚ n)
    (target : Fin n) (rounds : ℕ) (v : Fin n) :
    (recover input weights target rounds v).value =
      BuyAtBulk.Computation.ShortestPath.recover input.graph (fun x => weights[x.val]) target rounds v := by
  induction rounds generalizing v with
  | zero => rfl
  | succ k ih =>
      simp only [recover, iterate_value, step_value]
      rw [BuyAtBulk.Computation.ShortestPath.recover]
      split
      · exact ih v
      · try simp only [edgeChoice_value, step_value, iterate_value]
        split
        · rename_i missing
          simp only [edgeChoice_value, step_value, iterate_value] at missing
          split
          · rfl
          · rename_i u found
            rw [missing] at found
            contradiction
        · rename_i u found
          simp only [edgeChoice_value, step_value, iterate_value] at found
          split
          · rename_i missing
            rw [found] at missing
            contradiction
          · rename_i u' found'
            have same : u' = u := Option.some.inj (found'.symm.trans found)
            subst u'
            simp only [ih]

/-- Includes every recomputed distance table, predecessor test, list-control
branch, input read and actual walk constructor emitted by recovery. -/
theorem recover_count (input : GraphEncoding n) (weights : Vector ℚ n)
    (target : Fin n) (rounds : ℕ) (v : Fin n) :
    (recover input weights target rounds v).events.length ≤
      (rounds + 1) ^ 2 * (10 * n ^ 2 + 30 * n + 30) := by
  induction rounds generalizing v with
  | zero => simp only [recover, List.length_cons, List.length_nil]; nlinarith
  | succ k ih =>
      have previous := iterate_count input weights target k
      have next := step_count input weights (iterate input weights target k).value
      have choice := edgeChoice_count input weights (iterate input weights target k).value v
        (step input weights (iterate input weights target k).value).value[v.val]
      simp only [recover]
      split
      · have recursive := ih v
        simp only [List.length_append, List.length_cons, List.length_nil, read, emit]
        nlinarith
      · split
        · have unused := ih v
          simp only [List.length_append, List.length_cons, List.length_nil, read, emit]
          nlinarith
        · rename_i u found
          have recursive := ih u
          simp only [List.length_append, List.length_cons, List.length_nil, read, emit]
          nlinarith

theorem edgeChoiceList_words (input : GraphEncoding n) (weights : Vector ℚ n)
    (old : Vector (WithTop ℚ) n) (v : Fin n) (value : WithTop ℚ) (vertices : List (Fin n)) (L B K : ℕ)
    (inputs : ∀ u : Fin n, (Code.ofRat weights[u.val]).bits ≤ L)
    (old_width : ∀ u : Fin n, width old[u.val] ≤ B) (value_width : width value ≤ K)
    (indices : n ≤ K) (budget : 2 * (L + B) + 9 ≤ K) :
    WordsWithin K (edgeChoiceList input weights old v value vertices).events := by
  have one : 1 ≤ K := by omega
  have vi : v.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt v.isLt |>.trans indices)
  have wi : (Code.ofRat weights[v.val]).bits ≤ K := (inputs v).trans (by omega)
  induction vertices with
  | nil => simp [edgeChoiceList, WordsWithin, one]
  | cons u rest ih =>
      have ui : u.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt u.isLt |>.trans indices)
      have oi : width old[u.val] ≤ K := (old_width u).trans (by omega)
      have sum_width := (addition_width weights[v.val] old[u.val] L B (inputs v) (old_width u)).trans budget
      have arithmetic := addition_words weights[v.val] old[u.val] L B K (inputs v) (old_width u) one (by omega)
      simp only [edgeChoiceList]
      split
      · split <;> simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil, read, emit,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true] <;> aesop
      · simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
        aesop

theorem edgeChoice_words (input : GraphEncoding n) (weights : Vector ℚ n)
    (old : Vector (WithTop ℚ) n) (v : Fin n) (value : WithTop ℚ) (L B K : ℕ)
    (inputs : ∀ u : Fin n, (Code.ofRat weights[u.val]).bits ≤ L)
    (old_width : ∀ u : Fin n, width old[u.val] ≤ B) (value_width : width value ≤ K)
    (indices : n ≤ K) (budget : 2 * (L + B) + 9 ≤ K) :
    WordsWithin K (edgeChoice input weights old v value).events := by
  have result := edgeChoiceList_words input weights old v value (List.finRange n) L B K inputs old_width value_width indices budget
  simpa only [edgeChoice, indexList_value, wordsWithin_append] using
    And.intro (indexList_words n K indices) result

theorem recover_words_upto (input : GraphEncoding n) (weights : Vector ℚ n)
    (target : Fin n) (R L K : ℕ) (constant : 5 ≤ L)
    (inputs : ∀ v : Fin n, (Code.ofRat weights[v.val]).bits + 1 ≤ L)
    (indices : n ≤ K) (depth : R ≤ K)
    (budget : 2 * (L + labelBudget R L) + 9 ≤ K) :
    ∀ rounds ≤ R, ∀ v : Fin n, WordsWithin K (recover input weights target rounds v).events := by
  have one : 1 ≤ K := by omega
  have old_le : labelBudget R L ≤ K := by omega
  have input_width (u : Fin n) : (Code.ofRat weights[u.val]).bits ≤ L :=
    (Nat.le_add_right _ 1).trans (inputs u)
  have label_width (k : ℕ) (bounded : k ≤ R) (u : Fin n) :
      width (iterate input weights target k).value[u.val] ≤ labelBudget R L := by
    rw [iterate_value]
    have width_bound := iterate_label_width input weights target k L constant inputs u
    unfold labelBudget
    nlinarith
  have index_width (u : Fin n) : u.val.size ≤ K :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt u.isLt |>.trans indices)
  intro rounds
  induction rounds with
  | zero =>
      intro _ v
      simp only [recover, wordsWithin_cons, wordsWithin_nil, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
      exact ⟨one, ⟨index_width v, index_width target⟩, one⟩
  | succ k ih =>
      intro bounded v
      have previous := iterate_words_upto input weights target R L K constant inputs indices depth budget k (by omega)
      have old_width := label_width k (by omega)
      have next := step_words input weights (iterate input weights target k).value L (labelBudget R L) K input_width old_width indices budget
      have next_width (u : Fin n) : width (step input weights (iterate input weights target k).value).value[u.val] ≤ K := by
        have label := label_width (k + 1) bounded u
        simpa only [iterate] using label.trans old_le
      have ki : k.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega : k ≤ K)
      have vi := index_width v
      have old_v := (old_width v).trans old_le
      have next_v := next_width v
      have choice := edgeChoice_words input weights (iterate input weights target k).value v
        (step input weights (iterate input weights target k).value).value[v.val]
        L (labelBudget R L) K input_width old_width next_v indices budget
      simp only [recover]
      split
      · have recursive := ih (by omega) v
        simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil, read, emit,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
        aesop
      · split
        · simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil, read, emit,
            List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
          aesop
        · rename_i u found
          have ui := index_width u
          have recursive := ih (by omega) u
          simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil, read, emit,
            List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
          aesop

theorem recover_words (input : GraphEncoding n) (weights : Vector ℚ n)
    (target : Fin n) (rounds L : ℕ) (constant : 5 ≤ L)
    (inputs : ∀ v : Fin n, (Code.ofRat weights[v.val]).bits + 1 ≤ L) (v : Fin n) :
    WordsWithin (2 * (L + labelBudget rounds L) + 9 + n + rounds)
      (recover input weights target rounds v).events := by
  apply recover_words_upto input weights target rounds L _ constant inputs (by omega) (by omega) (by omega) rounds le_rfl v

end BuyAtBulk.Computation.Runtime.ShortestPath
