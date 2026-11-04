import BuyAtBulk.Computation.Runtime.ZeroProjection

namespace BuyAtBulk.Computation.Runtime.StoredRounding
open BuyAtBulk.UpperBound
open Rational
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

theorem projectWalk_count (physical : Vector ℚ n) {s t : Fin n}
    (walk : (zeroGraph input.graph (fun v => physical[v.val])).Walk s t) :
    (projectWalk input physical walk).events.length ≤ 3*(walk.length+1) := by
  induction walk with
  | nil => simp[projectWalk]
  | cons edge tail ih =>
    simp only[projectWalk,List.length_append,List.length_cons,List.length_nil,SimpleGraph.Walk.length_cons]
    omega

theorem projectWalk_words (physical : Vector ℚ n) {s t : Fin n}
    (walk : (zeroGraph input.graph (fun v => physical[v.val])).Walk s t) :
    WordsWithin (n+1) (projectWalk input physical walk).events := by
  have vertex (v : Fin n) : v.val.size ≤ n+1 :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := v.isLt;omega)
  have one : 1 ≤ n+1 := by omega
  induction walk with
  | nil => simpa only[projectWalk,wordsWithin_cons,wordsWithin_nil,List.mem_singleton,forall_eq,and_true] using And.intro one (vertex _)
  | cons edge tail ih =>
    simp only[projectWalk,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_singleton,forall_eq,and_true]
    exact ⟨⟨⟨one,vertex _⟩,ih⟩,vertex _⟩

theorem projectEntry_count (physical : Vector ℚ n) (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (entry : ZeroEntry input physical source target lengths) :
    (projectEntry input physical source target lengths entry).events.length ≤ 3*(n+1)+4 := by
  have path_bound : entry.2.val.length ≤ n := by simpa using Nat.le_of_lt entry.2.property.length_lt
  have projected := projectWalk_count input physical entry.2.val
  simp only[projectEntry]
  split_ifs <;>simp only[projectPath,List.length_append,List.length_cons,List.length_nil,readRat,emit_length,zeroTest] <;>omega

theorem projectEntries_count (physical : Vector ℚ n) (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (entries : List (ZeroEntry input physical source target lengths)) :
    (projectEntries input physical source target lengths entries).events.length ≤ entries.length*(3*(n+1)+7)+1 := by
  induction entries with
  | nil => simp[projectEntries,emit]
  | cons entry rest ih =>
    have head := projectEntry_count input physical source target lengths entry
    simp only[projectEntries]
    split <;>simp only[List.length_append,List.length_cons,List.length_nil] <;>nlinarith

theorem projectEntry_words (physical : Vector ℚ n) (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (entry : ZeroEntry input physical source target lengths) (L : ℕ)
    (lengths_width : ∀ i : Fin h, (Code.ofRat lengths[i.val]).bits ≤ L) :
    WordsWithin (n+h+L+10) (projectEntry input physical source target lengths entry).events := by
  let K := n+h+L+10
  have one : 1 ≤ K := by dsimp[K];omega
  have ii : entry.1.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := entry.1.isLt;dsimp[K];omega)
  have scalar : (Code.ofRat lengths[entry.1.val]).bits ≤ K := (lengths_width entry.1).trans (by dsimp[K];omega)
  have projected := (projectWalk_words input physical entry.2.val).mono (show n+1 ≤ K by dsimp[K];omega)
  simp only[projectEntry]
  split_ifs <;>simp only[projectPath,readRat,zeroTest,emit,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
    List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true] <;>dsimp[K] at * <;>aesop <;>omega

theorem projectEntries_words (physical : Vector ℚ n) (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (entries : List (ZeroEntry input physical source target lengths)) (L : ℕ)
    (lengths_width : ∀ i : Fin h, (Code.ofRat lengths[i.val]).bits ≤ L) :
    WordsWithin (n+h+L+10) (projectEntries input physical source target lengths entries).events := by
  let K := n+h+L+10
  have one : 1 ≤ K := by dsimp[K];omega
  have index (i : Fin h) : i.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := i.isLt;dsimp[K];omega)
  induction entries with
  | nil => simpa[projectEntries,emit,wordsWithin_cons] using one
  | cons entry rest ih =>
    have head := projectEntry_words input physical source target lengths entry L lengths_width
    have ii := index entry.1
    simp only[projectEntries]
    split
    · simp only[wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_singleton,forall_eq,and_true]
      aesop
    · rename_i projected returned
      have pi := index projected.1
      simp only[wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_singleton,forall_eq,and_true]
      aesop

end BuyAtBulk.Computation.Runtime.StoredRounding
