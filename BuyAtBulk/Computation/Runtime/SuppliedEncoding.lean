import BuyAtBulk.Computation.Runtime.OriginalEncodingBridge
import BuyAtBulk.Computation.StoredOriginal.Input

/-! Explicit binary input for supplied-path rounding. The graph tables,
openings, complete weighted path list, and both parameters are encoded. -/
set_option autoImplicit false
namespace BuyAtBulk.Computation.Runtime.SuppliedEncoding
open Rational BuyAtBulk.Computation.StoredOriginal OriginalEncoding
variable {n resources h : ℕ} (tables : Tables n resources h)

abbrev Entry := StoredOriginal.Entry (G:=tables.graphData.graph) tables.graphData.source tables.graphData.target

def entryWords (entry : Entry tables) : List ℤ :=
  [(entry.1.val : ℤ),(entry.2.2.val.support.length : ℤ)]++rationalWords entry.2.1++
    entry.2.2.val.support.map (fun v => (v.val : ℤ))

def entriesWords (entries : List (Entry tables)) : List ℤ := entries.flatMap (entryWords tables)

def words (fractional : Fractional tables) (ratio r : ℕ) : List ℤ :=
  OriginalEncoding.words tables++rationalVectorWords fractional.opening++
    [(fractional.entries.length : ℤ),(ratio : ℤ),(r : ℤ)]++entriesWords tables fractional.entries

def inputSize (fractional : Fractional tables) (ratio r : ℕ) : ℕ := arrayBits (words tables fractional ratio r)

theorem original_le (fractional : Fractional tables) (ratio r : ℕ) :
    OriginalEncoding.inputSize tables≤ inputSize tables fractional ratio r := by
  simp only[inputSize,words,arrayBits_append,OriginalEncoding.inputSize]
  omega

theorem dimensions (fractional : Fractional tables) (ratio r : ℕ) :
    n+resources+h≤ inputSize tables fractional ratio r :=
  (OriginalEncoding.dimensions tables).trans (original_le tables fractional ratio r)

theorem opening_bits (fractional : Fractional tables) (ratio r : ℕ) (a : Fin resources) :
    (Code.ofRat fractional.opening[a.val]).bits≤ inputSize tables fractional ratio r := by
  have member := rationalVectorBits_member fractional.opening a
  simp only[inputSize,words,arrayBits_append,rationalVectorWords_bits]
  omega

theorem ratio_bits (fractional : Fractional tables) (ratio r : ℕ) :
    ratio.size≤ inputSize tables fractional ratio r := by
  simp only[inputSize,words,arrayBits_append]
  simp only[arrayBits,wordBits,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Int.natAbs_natCast]
  omega

theorem girth_bits (fractional : Fractional tables) (ratio r : ℕ) :
    r.size≤ inputSize tables fractional ratio r := by
  simp only[inputSize,words,arrayBits_append]
  simp only[arrayBits,wordBits,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Int.natAbs_natCast]
  omega

theorem entries_length_words (entries : List (Entry tables)) : entries.length≤(entriesWords tables entries).length := by
  induction entries with
  | nil => simp[entriesWords]
  | cons entry rest ih =>
    simp only[entriesWords,List.flatMap_cons,List.length_append,entryWords,List.length_cons,List.length_nil,
      rationalWords,List.length_map]
    change rest.length≤(entriesWords tables rest).length at ih
    dsimp only[entriesWords] at ih
    omega

theorem entries_count (fractional : Fractional tables) (ratio r : ℕ) :
    fractional.entries.length≤ inputSize tables fractional ratio r := by
  have length := entries_length_words tables fractional.entries
  have encoded := length_le_arrayBits (entriesWords tables fractional.entries)
  simp only[inputSize,words,arrayBits_append]
  omega

theorem entry_bits_le (entry : Entry tables) :
    (Code.ofRat entry.2.1).bits≤arrayBits (entryWords tables entry) := by
  simp only[entryWords,arrayBits_append,rationalWords_bits]
  omega

theorem entries_bits_member (entries : List (Entry tables)) (entry : Entry tables) (member : entry∈entries) :
    arrayBits (entryWords tables entry)≤arrayBits (entriesWords tables entries) := by
  induction entries with
  | nil => simp at member
  | cons first rest ih =>
    simp only[List.mem_cons] at member
    simp only[entriesWords,List.flatMap_cons,arrayBits_append]
    rcases member with rfl | member
    · omega
    · have tail := ih member
      dsimp only[entriesWords] at tail
      omega

theorem weight_bits (fractional : Fractional tables) (ratio r : ℕ) (entry : Entry tables)
    (member : entry∈fractional.entries) :
    (Code.ofRat entry.2.1).bits≤ inputSize tables fractional ratio r := by
  have leaf := entry_bits_le tables entry
  have entries := entries_bits_member tables fractional.entries entry member
  simp only[inputSize,words,arrayBits_append]
  omega

theorem buying_bits (fractional : Fractional tables) (ratio r : ℕ) (a : Fin resources) :
    (Code.ofRat tables.buying[a.val]).bits≤ inputSize tables fractional ratio r :=
  (OriginalEncoding.buying_bits tables a).trans (original_le tables fractional ratio r)

theorem physical_bits (fractional : Fractional tables) (ratio r : ℕ) (a : Fin resources) :
    (Code.ofRat tables.length[a.val]).bits≤ inputSize tables fractional ratio r :=
  (OriginalEncoding.length_bits tables a).trans (original_le tables fractional ratio r)

theorem demand_bits (fractional : Fractional tables) (ratio r : ℕ) (i : Fin h) :
    (Code.ofRat tables.demand[i.val]).bits≤ inputSize tables fractional ratio r :=
  (OriginalEncoding.demand_bits tables i).trans (original_le tables fractional ratio r)

end BuyAtBulk.Computation.Runtime.SuppliedEncoding
