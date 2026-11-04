import BuyAtBulk.Computation.Runtime.FlowSearch

namespace BuyAtBulk.Computation.Runtime.FlowSearch
open Rational
variable {n : ℕ} (input : Computation.ShortestPath.GraphEncoding n)

private theorem index_word (v : Fin n) (K : ℕ) (indices : n≤K) : v.val.size≤K :=
  (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)

theorem concat_words {s u v : Fin n} (walk : input.graph.Walk s u) (edge : input.graph.Adj u v)
    (K : ℕ) (indices : n≤K) (one : 1≤K) : WordsWithin K (concat input walk edge).events := by
  induction walk with
  | nil => simp [concat,WordsWithin,index_word _ K indices,one]
  | @cons s t u first tail ih =>
      have tail := ih edge
      simp only [concat,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,
        List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
      exact ⟨⟨one,tail⟩,index_word s K indices⟩

theorem lookup_words {source target : Fin n} (table : FlowDecomposition.Table input.graph source)
    (K : ℕ) (indices : n≤K) (one : 1≤K) : WordsWithin K (lookup input table target).events := by
  induction table with
  | nil => simp [lookup,WordsWithin,one]
  | cons entry rest ih =>
    rcases entry with ⟨v,path⟩
    by_cases equal : v=target <;>
      simp [lookup,equal,WordsWithin,index_word _ K indices,one] at *
    all_goals aesop

theorem extend_words (matrix : FlowDecomposition.FlowMatrix n) {source target : Fin n}
    (table : FlowDecomposition.Table input.graph source) (K : ℕ) (indices : n≤K) (constant : 3≤K)
    (cells : ∀ u v : Fin n, (Code.ofRat matrix[u.val][v.val]).bits≤K) :
    WordsWithin K (extend input matrix table target).events := by
  have one : 1≤K := by omega
  have dimension : n.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans indices
  have zero : (Code.ofRat (0:ℚ)).bits=3 := by decide
  induction table with
  | nil => simp [extend,WordsWithin]; omega
  | cons entry rest ih =>
    rcases entry with ⟨v,path⟩
    have vi := index_word v K indices
    have ti := index_word target K indices
    have q := cells v target
    by_cases edge : input.graph.Adj v target
    · by_cases positive : 0<matrix[v.val][target.val]
      · have appended := concat_words input path edge K indices (by omega)
        simp only [extend,dif_pos edge,if_pos positive,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
          List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true,zero]
        aesop
      · simp only [extend,dif_pos edge,if_neg positive,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
          List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true,zero]
        aesop
    · simp only [extend,dif_neg edge,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
        List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
      aesop

theorem next_words (matrix : FlowDecomposition.FlowMatrix n) {source target : Fin n}
    (table : FlowDecomposition.Table input.graph source) (K : ℕ) (indices : n≤K) (constant : 3≤K)
    (cells : ∀ u v : Fin n, (Code.ofRat matrix[u.val][v.val]).bits≤K) :
    WordsWithin K (next input matrix table target).events := by
  have one : 1≤K := by omega
  have found := lookup_words input (target:=target) table K indices (by omega)
  have extended := extend_words input matrix (target:=target) table K indices constant cells
  simp only [next]
  split <;> simp only [wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,
    List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
  all_goals aesop

theorem collect_words (matrix : FlowDecomposition.FlowMatrix n) {source : Fin n}
    (table : FlowDecomposition.Table input.graph source) (targets : List (Fin n))
    (K : ℕ) (indices : n≤K) (constant : 3≤K)
    (cells : ∀ u v : Fin n, (Code.ofRat matrix[u.val][v.val]).bits≤K) :
    WordsWithin K (collect input matrix table targets).events := by
  induction targets with
  | nil => simp [collect,WordsWithin]; omega
  | cons target rest ih =>
    have one : 1≤K := by omega
    have found := next_words input matrix (target:=target) table K indices constant cells
    have ti := index_word target K indices
    simp only [collect]
    split <;> simp only [wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,
      List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
    all_goals aesop

theorem step_words (matrix : FlowDecomposition.FlowMatrix n) {source : Fin n}
    (table : FlowDecomposition.Table input.graph source) (K : ℕ) (indices : n≤K) (constant : 3≤K)
    (cells : ∀ u v : Fin n, (Code.ofRat matrix[u.val][v.val]).bits≤K) :
    WordsWithin K (step input matrix table).events := by
  have index := indexList_words n K indices
  have collected := collect_words input matrix table (List.finRange n) K indices constant cells
  simpa only [step,Traced.bind_events,Traced.bind_value,indexList_value,wordsWithin_append] using And.intro index collected

theorem iterate_words (matrix : FlowDecomposition.FlowMatrix n) (source : Fin n) (rounds K : ℕ)
    (indices : n≤K) (constant : 3≤K) (roundsBound : rounds≤K)
    (cells : ∀ u v : Fin n, (Code.ofRat matrix[u.val][v.val]).bits≤K) :
    WordsWithin K (iterate input matrix source rounds).events := by
  induction rounds with
  | zero => simp [iterate,WordsWithin,index_word _ K indices]; omega
  | succ rounds ih =>
    have previous := ih (by omega) cells
    have counter : rounds.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
    have stepped := step_words input matrix (iterate input matrix source rounds).value K indices constant cells
    simpa only [iterate,Traced.bind_events,Traced.bind_value,emit,wordsWithin_append,wordsWithin_cons,
      wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true] using
      And.intro counter (And.intro previous stepped)

theorem positivePath_words (matrix : FlowDecomposition.FlowMatrix n) (source target : Fin n) (K : ℕ)
    (indices : n≤K) (constant : 3≤K)
    (cells : ∀ u v : Fin n, (Code.ofRat matrix[u.val][v.val]).bits≤K) :
    WordsWithin K (positivePath input matrix source target).events := by
  have one : 1≤K := by omega
  have table := iterate_words input matrix source n K indices constant indices cells
  have one : 1≤K := by omega
  have found := lookup_words input (target:=target) (iterate input matrix source n).value K indices (by omega)
  simp only [positivePath]
  split
  · simp only [wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
      or_false,forall_eq_or_imp,forall_eq,and_true]
    aesop
  · rename_i walk returned
    have erased := Paths.toPath_words walk K indices (by omega)
    simp only [wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
      or_false,forall_eq_or_imp,forall_eq,and_true]
    aesop

end BuyAtBulk.Computation.Runtime.FlowSearch
