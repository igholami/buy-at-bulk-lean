import BuyAtBulk.Computation.Runtime.Batch

namespace BuyAtBulk.Computation.Runtime.StoredBatch
open BuyAtBulk.UpperBound
open Rational
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

def scalarInputBudget (L : ℕ) := 4*L+8

def metadataBudget (h L : ℕ) := StoredServe.metadataBudget h (scalarInputBudget L)

theorem run_metadata (buying physical : Vector ℚ n) (budget : ℚ) (ratio : ℕ) (thresholdFactor : ℚ)
    (source target : Vector (Fin n) h) (allowance : Vector ℚ h) (order : List (Fin h))
    (before : StoredState.State input.graph) (L : ℕ) (ratio_ge : 2 ≤ ratio)
    (budget_width : (Code.ofRat budget).bits ≤ L) (ratio_width : ratio.size ≤ L)
    (initial : StoredAttachment.Metadata input (fun q => (Code.ofRat q).bits ≤ metadataBudget h L) before) :
    StateProperty input source target (StoredAttachment.Metadata input (fun q => (Code.ofRat q).bits ≤ metadataBudget h L))
      (run input buying physical budget ratio thresholdFactor source target allowance order before).value := by
  induction order generalizing before with
  | nil => exact initial
  | cons i rest ih =>
      have served_meta := StoredServe.run_metadata input buying physical budget allowance[i.val] h ratio (ratMul thresholdFactor allowance[i.val]).value
        source[i.val] target[i.val] before (scalarInputBudget L) ratio_ge
        (budget_width.trans (by unfold scalarInputBudget; omega)) (ratio_width.trans (by unfold scalarInputBudget; omega)) initial
      simp only [run]
      split
      · trivial
      · rename_i middle route returned
        simp only [returned, StoredServe.StateProperty] at served_meta
        have next := ih middle served_meta
        split
        · trivial
        · rename_i after entries later
          simpa only [later, StateProperty] using next

def wordBudget (n h L : ℕ) := StoredServe.serveWordBudget n h (scalarInputBudget L)+n+h+4*L+20

theorem run_words (buying physical : Vector ℚ n) (budget : ℚ) (ratio : ℕ) (thresholdFactor : ℚ)
    (source target : Vector (Fin n) h) (allowance : Vector ℚ h) (order : List (Fin h))
    (before : StoredState.State input.graph) (L : ℕ) (constant : 8 ≤ L) (ratio_ge : 2 ≤ ratio)
    (buying_width : ∀ x : Fin n, (Code.ofRat buying[x.val]).bits ≤ L)
    (physical_width : ∀ x : Fin n, (Code.ofRat physical[x.val]).bits ≤ L)
    (budget_width : (Code.ofRat budget).bits ≤ L) (allowance_width : ∀ i : Fin h, (Code.ofRat allowance[i.val]).bits ≤ L)
    (threshold_width : (Code.ofRat thresholdFactor).bits ≤ L) (ratio_width : ratio.size ≤ L)
    (initial : StoredAttachment.Metadata input (fun q => (Code.ofRat q).bits ≤ metadataBudget h L) before) :
    WordsWithin (wordBudget n h L) (run input buying physical budget ratio thresholdFactor source target allowance order before).events := by
  let K := wordBudget n h L
  have input_bound : L ≤ scalarInputBudget L := by unfold scalarInputBudget; omega
  have one : 1 ≤ K := by dsimp [K, wordBudget]; omega
  have ni : n ≤ K := by dsimp [K, wordBudget]; omega
  have hi : h ≤ K := by dsimp [K, wordBudget]; omega
  have scalar : L ≤ K := by dsimp [K, wordBudget]; omega
  induction order generalizing before with
  | nil => simpa only [run, wordsWithin_cons, wordsWithin_nil, List.mem_singleton, forall_eq, and_true] using And.intro one one
  | cons i rest ih =>
      have threshold_bits : (Code.ofRat (ratMul thresholdFactor allowance[i.val]).value).bits ≤ scalarInputBudget L := by
        rw [ratMul_value]
        have actual := ratMul_result_bits thresholdFactor allowance[i.val]
        unfold scalarInputBudget
        have allowance_bits := allowance_width i
        omega
      have threshold_trace : WordsWithin K (ratMul thresholdFactor allowance[i.val]).events := by
        intro event member word present
        have actual := ratMul_words thresholdFactor allowance[i.val] event member word present
        have allowance_bits := allowance_width i
        dsimp [K, wordBudget]
        omega
      have served_trace := (StoredServe.run_words input buying physical budget allowance[i.val] h ratio (ratMul thresholdFactor allowance[i.val]).value
        source[i.val] target[i.val] before (scalarInputBudget L) (by unfold scalarInputBudget; omega) ratio_ge
        (fun x => (buying_width x).trans input_bound) (fun x => (physical_width x).trans input_bound)
        (budget_width.trans input_bound) ((allowance_width i).trans input_bound) threshold_bits (ratio_width.trans input_bound) initial).mono
        (show StoredServe.serveWordBudget n h (scalarInputBudget L) ≤ K by dsimp [K, wordBudget]; omega)
      have served_meta := StoredServe.run_metadata input buying physical budget allowance[i.val] h ratio (ratMul thresholdFactor allowance[i.val]).value
        source[i.val] target[i.val] before (scalarInputBudget L) ratio_ge (budget_width.trans input_bound)
        (ratio_width.trans input_bound) initial
      have ii := ((Nat.size_le.mpr Nat.lt_two_pow_self : i.val.size ≤ i.val).trans (Nat.le_of_lt i.isLt)).trans hi
      have si := ((Nat.size_le.mpr Nat.lt_two_pow_self : source[i.val].val.size ≤ source[i.val].val).trans (Nat.le_of_lt source[i.val].isLt)).trans ni
      have ti := ((Nat.size_le.mpr Nat.lt_two_pow_self : target[i.val].val.size ≤ target[i.val].val).trans (Nat.le_of_lt target[i.val].isLt)).trans ni
      have ai := (allowance_width i).trans scalar
      have fi := threshold_width.trans scalar
      simp only [run]
      split
      · simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
          or_false, forall_eq_or_imp, forall_eq, and_true]
        aesop
      · rename_i middle route returned
        simp only [returned, StoredServe.StateProperty] at served_meta
        have next := ih middle served_meta
        split <;> simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
          or_false, forall_eq_or_imp, forall_eq, and_true] <;> aesop

end BuyAtBulk.Computation.Runtime.StoredBatch
