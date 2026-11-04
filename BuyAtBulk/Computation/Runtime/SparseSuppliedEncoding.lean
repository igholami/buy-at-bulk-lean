import BuyAtBulk.Computation.Runtime.SuppliedEncoding

/-! Binary size bounds for returned sparse original-path lists. -/
namespace BuyAtBulk.Computation.Runtime.SparseSupplied
open Rational StoredOriginal OriginalEncoding
variable {n resources h : ℕ} (tables : Tables n resources h)

def entryBitBudget (n h L : ℕ) := 2*h+2*n+2*L+4+n*(2*n+2)

theorem entry_encoding_bound (entry : SuppliedEncoding.Entry tables) (L : ℕ)
    (bits : (Code.ofRat entry.2.1).bits ≤ L) :
    arrayBits (SuppliedEncoding.entryWords tables entry) ≤ entryBitBudget n h L := by
  have requestBound : entry.1.val < h := entry.1.isLt
  have request : entry.1.val.size ≤ h :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have pathLength : entry.2.2.val.support.length ≤ n := by
    have := entry.2.2.property.length_lt
    simp only [Fintype.card_fin] at this
    simp only [SimpleGraph.Walk.length_support]
    omega
  have lengthBits : entry.2.2.val.support.length.size ≤ n :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans pathLength
  have vertexBits : ∀ v ∈ entry.2.2.val.support, wordBits (v.val : ℤ) ≤ 2*n+2 := by
    intro v _
    have size : v.val.size ≤ n := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
    simpa only [wordBits, Int.natAbs_natCast] using Nat.add_le_add_right (Nat.mul_le_mul_left 2 size) 2
  have tail : arrayBits (entry.2.2.val.support.map fun v => (v.val : ℤ)) ≤ n*(2*n+2) := by
    unfold arrayBits
    rw [List.map_map]
    apply (List.sum_le_length_nsmul _ _ (by
      intro q member
      obtain ⟨v,mem,rfl⟩ := List.mem_map.mp member
      exact vertexBits v mem)).trans
    simpa only [List.length_map, nsmul_eq_mul, Nat.cast_id] using Nat.mul_le_mul_right (2*n+2) pathLength
  have front : arrayBits [(entry.1.val : ℤ),(entry.2.2.val.support.length : ℤ)] ≤ 2*h+2*n+4 := by
    simp only [arrayBits,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,wordBits,Int.natAbs_natCast]
    omega
  change arrayBits ([(entry.1.val : ℤ),(entry.2.2.val.support.length : ℤ)] ++
    rationalWords entry.2.1 ++ entry.2.2.val.support.map (fun v => (v.val : ℤ))) ≤ _
  rw [arrayBits_append,arrayBits_append,rationalWords_bits]
  calc
    _ ≤ (2*h+2*n+4)+2*L+n*(2*n+2) :=
      Nat.add_le_add (Nat.add_le_add front (Nat.mul_le_mul_left 2 bits)) tail
    _ = _ := by unfold entryBitBudget; ring

theorem entries_encoding_bound (entries : List (SuppliedEncoding.Entry tables)) (L : ℕ)
    (bits : ∀ e∈entries,(Code.ofRat e.2.1).bits ≤ L) :
    arrayBits (SuppliedEncoding.entriesWords tables entries) ≤ entries.length*entryBitBudget n h L := by
  induction entries with
  | nil => simp [SuppliedEncoding.entriesWords,arrayBits]
  | cons e rest ih =>
    have head := entry_encoding_bound tables e L (bits e (by simp))
    have tail := ih (fun e mem=>bits e (by simp[mem]))
    simp only [SuppliedEncoding.entriesWords,List.flatMap_cons,arrayBits_append,List.length_cons]
    change arrayBits (SuppliedEncoding.entryWords tables e) +
      arrayBits (SuppliedEncoding.entriesWords tables rest) ≤ _
    nlinarith

theorem output_encoding_bound (input output : Fractional tables)
    (opening : output.opening=input.opening) (K L : ℕ) (count : output.entries.length ≤ K)
    (bits : ∀ e∈output.entries,(Code.ofRat e.2.1).bits ≤ L) :
    SuppliedEncoding.inputSize tables output 8 1 ≤
      SuppliedEncoding.inputSize tables input 8 1 + 2*K+16+K*entryBitBudget n h L := by
  have entries := entries_encoding_bound tables output.entries L bits
  have encoded := Nat.mul_le_mul_right (entryBitBudget n h L) count
  have countBits : output.entries.length.size ≤ K :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans count
  have base : arrayBits (OriginalEncoding.words tables) +
      arrayBits (rationalVectorWords input.opening) ≤ SuppliedEncoding.inputSize tables input 8 1 := by
    simp only [SuppliedEncoding.inputSize,SuppliedEncoding.words,arrayBits_append]
    omega
  have header : arrayBits [(output.entries.length : ℤ),(8 : ℤ),(1 : ℤ)] ≤ 2*K+16 := by
    simp only [arrayBits,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,wordBits,Int.natAbs_natCast]
    change 2*output.entries.length.size+2+(2*4+2+(2*1+2+0)) ≤ 2*K+16
    omega
  change arrayBits (OriginalEncoding.words tables ++ rationalVectorWords output.opening ++
    [(output.entries.length : ℤ),(8 : ℤ),(1 : ℤ)] ++ SuppliedEncoding.entriesWords tables output.entries) ≤ _
  rw [arrayBits_append,arrayBits_append,arrayBits_append,opening]
  omega

end BuyAtBulk.Computation.Runtime.SparseSupplied
