import BuyAtBulk.Computation.Runtime.ZeroRestriction

namespace BuyAtBulk.Computation.Runtime.StoredRounding
open BuyAtBulk.UpperBound
open Rational
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

abbrev PositiveEntry (source target : Vector (Fin n) h) (lengths : Vector ℚ h) :=
  Σ i : Fin h, input.graph.Path source[i.val]
    (Rounding.positiveTarget (fun i => source[i.val]) (fun i => target[i.val]) (fun i => lengths[i.val]) i)

def projectPositiveEntry (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (entry : PositiveEntry input source target lengths) : Traced (Option (StoredBatch.Entry input source target)) :=
  let length := readRat lengths entry.1
  let test := zeroTest length.value
  let prefixEvents := length.events++test.events++[⟨Operation.branch,[1]⟩]
  if guard : test.value=false then
    have positive : lengths[entry.1.val]≠0 := of_decide_eq_false guard
    let copied := ShortestPath.copyPath entry.2 rfl (by simp only[Rounding.positiveTarget,if_neg positive])
    ⟨some ⟨entry.1,copied⟩,prefixEvents++[⟨.cons,[entry.1.val.size]⟩]⟩
  else ⟨none,prefixEvents⟩

theorem projectPositiveEntry_value (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (entry : PositiveEntry input source target lengths) :
    (projectPositiveEntry input source target lengths entry).value=
      Rounding.projectPositiveEntry input.graph (fun i => source[i.val]) (fun i => target[i.val])
        (fun i => lengths[i.val]) entry := by
  simp only[projectPositiveEntry,Rounding.projectPositiveEntry]
  by_cases zero : lengths[entry.1.val]=0 <;>simp[zero,zeroTest,readRat]


def projectPositiveEntries (source target : Vector (Fin n) h) (lengths : Vector ℚ h) :
    List (PositiveEntry input source target lengths) → Traced (List (StoredBatch.Entry input source target))
  | [] => emit .cons [1] []
  | entry::rest =>
    let head := projectPositiveEntry input source target lengths entry
    let tail := projectPositiveEntries source target lengths rest
    let events := [⟨Operation.scan,[entry.1.val.size]⟩]++head.events++tail.events++[⟨.branch,[1]⟩]
    match head.value with
    | none => ⟨tail.value,events⟩
    | some projected => ⟨projected::tail.value,events++[⟨.cons,[projected.1.val.size]⟩]⟩

theorem projectPositiveEntries_value (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (entries : List (PositiveEntry input source target lengths)) :
    (projectPositiveEntries input source target lengths entries).value=
      Rounding.projectPositiveEntries input.graph (fun i => source[i.val]) (fun i => target[i.val])
        (fun i => lengths[i.val]) entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only[Rounding.projectPositiveEntries,←projectPositiveEntry_value] at ih
    simp only[projectPositiveEntries,Rounding.projectPositiveEntries,List.filterMap_cons,←projectPositiveEntry_value]
    split <;>simp_all

theorem projectPositiveEntry_count (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (entry : PositiveEntry input source target lengths) :
    (projectPositiveEntry input source target lengths entry).events.length ≤ 4 := by
  simp only[projectPositiveEntry]
  split_ifs <;>simp only[List.length_append,List.length_cons,List.length_nil,readRat,emit_length,zeroTest] <;>omega

theorem projectPositiveEntries_count (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (entries : List (PositiveEntry input source target lengths)) :
    (projectPositiveEntries input source target lengths entries).events.length ≤ entries.length*7+1 := by
  induction entries with
  | nil => simp[projectPositiveEntries,emit]
  | cons entry rest ih =>
    have head := projectPositiveEntry_count input source target lengths entry
    simp only[projectPositiveEntries]
    split <;>simp only[List.length_append,List.length_cons,List.length_nil] <;>nlinarith

theorem projectPositiveEntry_words (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (entry : PositiveEntry input source target lengths) (L : ℕ)
    (lengths_width : ∀ i : Fin h, (Code.ofRat lengths[i.val]).bits ≤ L) :
    WordsWithin (n+h+L+10) (projectPositiveEntry input source target lengths entry).events := by
  let K := n+h+L+10
  have one : 1 ≤ K := by dsimp[K];omega
  have ii : entry.1.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := entry.1.isLt;dsimp[K];omega)
  have scalar : (Code.ofRat lengths[entry.1.val]).bits ≤ K := (lengths_width entry.1).trans (by dsimp[K];omega)
  simp only[projectPositiveEntry]
  split_ifs <;>simp only[readRat,zeroTest,emit,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
    List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true] <;>dsimp[K] at * <;>aesop <;>omega

theorem projectPositiveEntries_words (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (entries : List (PositiveEntry input source target lengths)) (L : ℕ)
    (lengths_width : ∀ i : Fin h, (Code.ofRat lengths[i.val]).bits ≤ L) :
    WordsWithin (n+h+L+10) (projectPositiveEntries input source target lengths entries).events := by
  let K := n+h+L+10
  have one : 1 ≤ K := by dsimp[K];omega
  have index (i : Fin h) : i.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := i.isLt;dsimp[K];omega)
  induction entries with
  | nil => simpa[projectPositiveEntries,emit,wordsWithin_cons] using one
  | cons entry rest ih =>
    have head := projectPositiveEntry_words input source target lengths entry L lengths_width
    have ii := index entry.1
    simp only[projectPositiveEntries]
    split
    · simp only[wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_singleton,forall_eq,and_true]
      aesop
    · rename_i projected returned
      have pi := index projected.1
      simp only[wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_singleton,forall_eq,and_true]
      aesop

theorem projectPositiveEntries_length (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (entries : List (PositiveEntry input source target lengths)) :
    (projectPositiveEntries input source target lengths entries).value.length ≤ entries.length := by
  rw [projectPositiveEntries_value]
  exact List.length_filterMap_le _ _

end BuyAtBulk.Computation.Runtime.StoredRounding
