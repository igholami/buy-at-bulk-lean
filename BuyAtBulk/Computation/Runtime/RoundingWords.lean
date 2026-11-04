import BuyAtBulk.Computation.Runtime.Rounding

namespace BuyAtBulk.Computation.Runtime.StoredRounding
open Rational
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

def roundingWords (n h L : ℕ) := freeWords n h L+zeroWords n h L+
  positiveWords n h L+n+h+phaseScalarBudget L+L+100

theorem run_words (buying physical opening : Vector ℚ n) (budget : ℚ) (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (ratio r : ℕ) (ratio_ge : 2 ≤ ratio) (L : ℕ) (constant : 8 ≤ L)
    (buying_width : ∀ v : Fin n, (Code.ofRat buying[v.val]).bits ≤ L)
    (physical_width : ∀ v : Fin n, (Code.ofRat physical[v.val]).bits ≤ L)
    (opening_width : ∀ v : Fin n, (Code.ofRat opening[v.val]).bits ≤ L)
    (budget_width : (Code.ofRat budget).bits ≤ L) (lengths_width : ∀ i : Fin h, (Code.ofRat lengths[i.val]).bits ≤ L)
    (ratio_width : ratio.size ≤ L) (r_width : r.size ≤ L) :
    WordsWithin (roundingWords n h L) (run input buying physical opening budget source target lengths ratio r ratio_ge).events := by
  let K := roundingWords n h L
  let S := positiveInputBudget L
  have LS : L ≤ S := by dsimp[S,positiveInputBudget,phaseScalarBudget];omega
  have ni : n ≤ K := by dsimp[K,roundingWords];omega
  have hi : h ≤ K := by dsimp[K,roundingWords];omega
  have one : 1 ≤ K := by dsimp[K,roundingWords];omega
  have three : 3 ≤ K := by dsimp[K,roundingWords];omega
  have nn := (Nat.size_le.mpr Nat.lt_two_pow_self : n.size ≤ n).trans ni
  have hh := (Nat.size_le.mpr Nat.lt_two_pow_self : h.size ≤ h).trans hi
  have scalar := budget_width.trans (show L ≤ K by dsimp[K,roundingWords];omega)
  have free := (freeRun_words input buying physical source target lengths L constant buying_width physical_width lengths_width).mono
    (show freeWords n h L ≤ K by dsimp[K,roundingWords];omega)
  have zero := (zeroRun_words input buying physical opening budget source target lengths L constant buying_width physical_width opening_width
    budget_width lengths_width).mono (show zeroWords n h L ≤ K by dsimp[K,roundingWords];omega)
  simp only[run]
  split
  · have flags := (constantVector_words n false 1).mono (show n+1+1 ≤ K by dsimp[K,roundingWords];omega)
    simp only[emit,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
    aesop
  · split
    · simp only[emit,zeroTest,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
      aesop
    · split
      · simp only[emit,zeroTest,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
        aesop
      · rename_i zeroAfter zeroEntries zeros
        have positive := (positiveRun_words input buying physical opening budget source target lengths
          ratio r zeroAfter.bought ratio_ge L constant buying_width physical_width opening_width budget_width lengths_width
          ratio_width r_width).mono (show positiveWords n h L ≤ K by dsimp[K,roundingWords];omega)
        split
        · simp only[emit,zeroTest,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
          aesop
        · rename_i after entries positives
          have projected := (projectEntries_words input physical source target lengths zeroEntries L lengths_width).mono
            (show n+h+L+10 ≤ K by dsimp[K,roundingWords];omega)
          have combined := (appendEntries_words input source target (projectEntries input physical source target lengths zeroEntries).value entries).mono
            (show h+1 ≤ K by dsimp[K,roundingWords];omega)
          simp only[emit,zeroTest,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
          aesop

end BuyAtBulk.Computation.Runtime.StoredRounding
