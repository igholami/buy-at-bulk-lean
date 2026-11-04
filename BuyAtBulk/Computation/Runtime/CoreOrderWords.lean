import BuyAtBulk.Computation.Runtime.CoreOrderCost

namespace BuyAtBulk.Computation.Runtime.StoredCore.Order
open Rational
variable {h : ℕ}

private theorem index_bound (i : Fin h) : i.val.size ≤ h :=
  (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt i.isLt)

theorem length_words (indices : List (Fin h)) : WordsWithin (h+indices.length+2) (length indices).events := by
  induction indices with
  | nil => simp[length,emit,WordsWithin]
  | cons i rest ih =>
    have ii := index_bound i
    have old : rest.length.size ≤ rest.length := Nat.size_le.mpr Nat.lt_two_pow_self
    have next : (rest.length+1).size ≤ rest.length+1 := Nat.size_le.mpr Nat.lt_two_pow_self
    have tail := ih.mono (show h+rest.length+2 ≤ h+(i::rest).length+2 by simp)
    simp only[length,length_value,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
      or_false,forall_eq_or_imp,forall_eq,and_true,List.length_cons] at *
    aesop <;> omega

theorem splitAt_words (k : ℕ) (indices : List (Fin h)) : WordsWithin (h+1) (splitAt k indices).events := by
  induction k generalizing indices with
  | zero => simp[splitAt,emit,WordsWithin]
  | succ k ih =>
    cases indices with
    | nil => simp[splitAt,emit,WordsWithin]
    | cons i rest =>
      have tail := ih rest
      have ii := index_bound i
      simp only[splitAt,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_singleton,forall_eq,and_true]
      exact ⟨⟨by omega,tail⟩,by omega⟩

theorem merge_words (allowance : Vector ℚ h) (left right : List (Fin h)) (L : ℕ)
    (inputs : ∀ i : Fin h, (Code.ofRat allowance[i.val]).bits ≤ L) :
    WordsWithin (h+L+2) (merge allowance left right).events := by
  fun_induction merge allowance left right
  all_goals
    simp_all +zetaDelta only[merge,readRat,ratLe,emit_value,emit,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
      List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
    repeat' apply And.intro
    all_goals (first | assumption | exact (inputs _).trans (by omega) | exact (index_bound _).trans (by omega) | omega)

theorem sort_words (allowance : Vector ℚ h) (fuel : ℕ) (indices : List (Fin h)) (L N : ℕ)
    (inputs : ∀ i : Fin h, (Code.ofRat allowance[i.val]).bits ≤ L) (length_bound : indices.length ≤ N) :
    WordsWithin (h+L+N+5) (sort allowance fuel indices).events := by
  let K := h+L+N+5
  have one : 1 ≤ K := by dsimp[K];omega
  induction fuel generalizing indices with
  | zero => simpa only[sort,emit,wordsWithin_cons,wordsWithin_nil,List.mem_singleton,forall_eq,and_true] using one
  | succ k ih =>
    match indices with
    | [] => simpa only[sort,emit,wordsWithin_cons,wordsWithin_nil,List.mem_singleton,forall_eq,and_true] using one
    | [i] => simpa only[sort,emit,wordsWithin_cons,wordsWithin_nil,List.mem_singleton,forall_eq,and_true] using one
    | i::j::rest =>
      let xs := i::j::rest
      let q := (xs.length+1)/2
      let left := (xs.splitAt q).1
      let right := (xs.splitAt q).2
      have xs_bound : xs.length ≤ N := length_bound
      have left_bound : left.length ≤ N := by simp only[left,List.splitAt_eq,List.length_take];dsimp[xs] at *;omega
      have right_bound : right.length ≤ N := by simp only[right,List.splitAt_eq,List.length_drop];dsimp[xs] at *;omega
      have counted := (length_words xs).mono (show h+xs.length+2 ≤ K by dsimp[K];omega)
      have divided := (splitAt_words q xs).mono (show h+1 ≤ K by dsimp[K];omega)
      have Ltrace := ih left left_bound
      have Rtrace := ih right right_bound
      have combined := (merge_words allowance (sort allowance k left).value (sort allowance k right).value L inputs).mono
        (show h+L+2 ≤ K by dsimp[K];omega)
      have si : xs.length.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[K];omega)
      have ai : (xs.length+1).size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[K];omega)
      have qi : q.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[K,q];omega)
      have two : 2 ≤ K := by dsimp[K];omega
      simp only[sort,length_value,emit_value,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
        List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true,emit]
      aesop

end BuyAtBulk.Computation.Runtime.StoredCore.Order
