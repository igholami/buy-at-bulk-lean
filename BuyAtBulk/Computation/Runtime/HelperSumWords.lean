import BuyAtBulk.Computation.Runtime.HelperScalarWords

namespace BuyAtBulk.Computation.Runtime.MaterializedHelper
open Rational BuyAtBulk.UpperBound
variable {n h ratio : ℕ}

def sumBudget (N L : ℕ) := 2*(2*N+1)*(L+1)+2

theorem buyingSum_bits (buying : Vector ℚ n) (vertices : List (Fin n)) (N L : ℕ)
    (constant : 5≤L) (length : vertices.length≤N)
    (inputs : ∀ v : Fin n, (Code.ofRat buying[v.val]).bits≤L) :
    (Code.ofRat (buyingSum buying vertices).value).bits≤sumBudget N L := by
  rw [buyingSum_value]
  have bound := HelperExpressions.sum_rat_bits (vertices.map fun v => buying[v.val]) (L+1) (by omega) (by
    intro q member
    obtain ⟨v,member,rfl⟩ := List.mem_map.mp member
    exact Nat.add_le_add_right (inputs v) 1)
  simp only [List.length_map] at bound
  exact bound.trans (by unfold sumBudget; nlinarith)

theorem buyingSum_words (buying : Vector ℚ n) (vertices : List (Fin n)) (N L K : ℕ)
    (constant : 5≤L) (length : vertices.length≤N) (indices : n≤K)
    (capacity : 2*(L+sumBudget N L)+8≤K)
    (inputs : ∀ v : Fin n, (Code.ofRat buying[v.val]).bits≤L) :
    WordsWithin K (buyingSum buying vertices).events := by
  induction vertices with
  | nil => simp [buyingSum,Traced.pure]
  | cons v rest ih =>
    have tail_length : rest.length≤N := by simpa using (Nat.le_trans (Nat.le_succ rest.length) length)
    have tail := ih tail_length inputs
    have bits := buyingSum_bits buying rest N L constant tail_length inputs
    have input := inputs v
    have vi : v.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
    have add := (show WordsWithin (2*((Code.ofRat buying[v.val]).bits+(Code.ofRat (buyingSum buying rest).value).bits)+8)
      (ratAdd buying[v.val] (buyingSum buying rest).value).events from ratAdd_words _ _).mono
        (show _≤K by omega)
    simp only [buyingSum,Traced.bind_events,Traced.bind_value,emit_value,readRat,emit,wordsWithin_append,
      wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
    exact ⟨vi,⟨vi,by omega⟩,tail,add⟩

theorem weightedTolls_bits (opening : Vector ℚ n) (database : Core.RowDatabase h ratio n)
    (raw : Core.RawRow h ratio) (vertices : List (Fin n)) (N L : ℕ) (constant : 5≤L)
    (length : vertices.length≤N) (inputs : ∀ v : Fin n, (Code.ofRat opening[v.val]).bits≤L)
    (tolls : ∀ v : Fin n, (Code.ofRat (Core.getRow database raw).toll[v.val]).bits≤L) :
    (Code.ofRat (Runtime.weightedTolls opening database raw vertices).value).bits≤sumBudget N (4*L+8) := by
  rw [Runtime.weightedTolls_value]
  have bound := HelperExpressions.sum_rat_bits
    (vertices.map fun v => opening[v.val]*(Core.getRow database raw).toll[v.val]) (4*L+9) (by omega) (by
      intro q member
      obtain ⟨v,member,rfl⟩ := List.mem_map.mp member
      have product := ratMul_result_bits opening[v.val] (Core.getRow database raw).toll[v.val]
      have a := inputs v
      have b := tolls v
      omega)
  simp only [List.length_map] at bound
  exact bound.trans (by unfold sumBudget; nlinarith)

theorem weightedTolls_words (opening : Vector ℚ n) (database : Core.RowDatabase h ratio n)
    (raw : Core.RawRow h ratio) (vertices : List (Fin n)) (N L K : ℕ) (constant : 5≤L)
    (length : vertices.length≤N) (indices : n+h+UpperBound.gridDepth h ratio+2≤K)
    (capacity : 2*(4*L+8+sumBudget N (4*L+8))+8≤K)
    (inputs : ∀ v : Fin n, (Code.ofRat opening[v.val]).bits≤L)
    (tolls : ∀ v : Fin n, (Code.ofRat (Core.getRow database raw).toll[v.val]).bits≤L) :
    WordsWithin K (Runtime.weightedTolls opening database raw vertices).events := by
  induction vertices with
  | nil => simp [Runtime.weightedTolls,Traced.pure]
  | cons v rest ih =>
    have tail_length : rest.length≤N := by simpa using (Nat.le_trans (Nat.le_succ rest.length) length)
    have tail := ih tail_length inputs tolls
    have bits := weightedTolls_bits opening database raw rest N L constant tail_length inputs tolls
    have a := inputs v
    have b := tolls v
    have product := ratMul_result_bits opening[v.val] (Core.getRow database raw).toll[v.val]
    have multiply := (wordBound_ratMul opening[v.val] (Core.getRow database raw).toll[v.val]).mono (show _≤K by omega)
    have add := (show WordsWithin
      (2*((Code.ofRat (opening[v.val]*(Core.getRow database raw).toll[v.val])).bits+
        (Code.ofRat (Runtime.weightedTolls opening database raw rest).value).bits)+8)
      (ratAdd (opening[v.val]*(Core.getRow database raw).toll[v.val])
        (Runtime.weightedTolls opening database raw rest).value).events from ratAdd_words _ _).mono (show _≤K by omega)
    have vi : v.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
    have ri : raw.1.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := raw.1.isLt; omega)
    have di : raw.2.2.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := raw.2.2.isLt; omega)
    simp only [Runtime.weightedTolls,Traced.bind_events,Traced.bind_value,Runtime.getRow,readRat,emit,
      ratMul_value,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
      or_false,forall_eq_or_imp,forall_eq,and_true]
    repeat' apply And.intro
    all_goals first | exact multiply | exact add | exact tail | omega

end BuyAtBulk.Computation.Runtime.MaterializedHelper
