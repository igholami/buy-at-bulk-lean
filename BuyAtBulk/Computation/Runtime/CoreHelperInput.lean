import BuyAtBulk.Computation.Runtime.CoreIncludedRuntime

namespace BuyAtBulk.Computation.Runtime.StoredCore
open BuyAtBulk.UpperBound
variable {h ratio : ℕ}

def rowLength : List (Core.RawRow h ratio) → Traced ℕ
  | [] => emit .write [0] 0
  | _::rest =>
    let next := rowLength rest
    ⟨next.value+1,[⟨.scan,[1]⟩]++next.events++[⟨.natAdd,[next.value.size,1,(next.value+1).size]⟩]⟩

@[simp] theorem rowLength_value (rows : List (Core.RawRow h ratio)) : (rowLength rows).value=rows.length := by
  induction rows <;>simp_all[rowLength]

@[simp] theorem rowLength_count (rows : List (Core.RawRow h ratio)) : (rowLength rows).events.length=2*rows.length+1 := by
  induction rows <;>simp_all[rowLength,emit,Nat.mul_add]

/-- Computes and caches the row count once, then copies scalar row fields into
an actual array. `zipIdx` in the trace describes each actual write position. -/
def rowsVector (rows : List (Core.RawRow h ratio)) : Traced (Σ m,Vector (Core.RawRow h ratio) m) :=
  let size := rowLength rows
  let cells : Vector (Core.RawRow h ratio) size.value := ⟨rows.toArray,by simp[size]⟩
  ⟨⟨size.value,cells⟩,size.events++[⟨.write,[0]⟩]++rows.zipIdx.flatMap (fun cell =>
    let raw := cell.1
    let k := cell.2
    [⟨.scan,[k.size]⟩,⟨.read,[raw.1.val.size]⟩,⟨.read,[1]⟩,⟨.read,[raw.2.2.val.size]⟩,
      ⟨.cons,[raw.1.val.size,1,raw.2.2.val.size]⟩,⟨.write,[k.size]⟩])++[⟨.cons,[size.value.size]⟩]⟩

@[simp] theorem rowsVector_length (rows : List (Core.RawRow h ratio)) : (rowsVector rows).value.1=rows.length := rowLength_value rows

private theorem map_get_rows {m : ℕ} (rows : List (Core.RawRow h ratio)) (same : m=rows.length)
    (valid : rows.toArray.size=m) :
    (List.finRange m).map (fun i => (⟨rows.toArray,valid⟩ : Vector (Core.RawRow h ratio) m)[i.val])=rows := by
  subst m
  rw[←List.ofFn_eq_map]
  simpa only[Vector.getElem_mk,List.getElem_toArray] using (List.ofFn_getElem (xs:=rows))

theorem rowsVector_image (rows : List (Core.RawRow h ratio)) :
    (List.finRange (rowsVector rows).value.1).map (fun i => (rowsVector rows).value.2[i.val])=rows := by
  exact map_get_rows rows (rowLength_value rows) _

@[simp] theorem rowsVector_count (rows : List (Core.RawRow h ratio)) :
    (rowsVector rows).events.length=8*rows.length+3 := by
  simp[rowsVector,List.length_flatMap,List.map_const',Nat.mul_comm]
  omega

theorem rowLength_words (rows : List (Core.RawRow h ratio)) :
    WordsWithin (rows.length+2) (rowLength rows).events := by
  induction rows with
  | nil => simp[rowLength,emit,WordsWithin]
  | cons raw rest ih =>
    have old : rest.length.size ≤ rest.length := Nat.size_le.mpr Nat.lt_two_pow_self
    have next : (rest.length+1).size ≤ rest.length+1 := Nat.size_le.mpr Nat.lt_two_pow_self
    have tail := ih.mono (show rest.length+2 ≤ (raw::rest).length+2 by simp)
    simp only[rowLength,rowLength_value,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
      or_false,forall_eq_or_imp,forall_eq,and_true,List.length_cons]
    aesop <;>omega

theorem rowsVector_words (rows : List (Core.RawRow h ratio)) :
    WordsWithin (rows.length+h+UpperBound.gridDepth h ratio+5) (rowsVector rows).events := by
  let K := rows.length+h+UpperBound.gridDepth h ratio+5
  have lengthTrace := (rowLength_words rows).mono (show rows.length+2 ≤ K by dsimp[K];omega)
  have countWord : (rowLength rows).value.size ≤ K := by rw[rowLength_value];exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[K];omega)
  have one : 1 ≤ K := by dsimp[K];omega
  simp only[rowsVector,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_singleton,forall_eq,and_true]
  refine ⟨⟨⟨lengthTrace,by omega⟩,?_⟩,countWord⟩
  apply words_flatMap
  intro cell member
  have index_bound : cell.2 < rows.length := by simpa using List.snd_lt_of_mem_zipIdx member
  have ii : cell.2.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[K];omega)
  have ri : cell.1.1.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := cell.1.1.isLt;dsimp[K];omega)
  have di : cell.1.2.2.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := cell.1.2.2.isLt;dsimp[K];omega)
  simp only[wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
  exact ⟨ii,ri,one,di,⟨ri,one,di⟩,ii⟩

end BuyAtBulk.Computation.Runtime.StoredCore
