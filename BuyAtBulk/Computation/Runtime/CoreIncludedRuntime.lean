import BuyAtBulk.Computation.Runtime.CoreIncludedRows

namespace BuyAtBulk.Computation.Runtime.StoredCore
open BuyAtBulk.UpperBound
variable {n h : ℕ}

def rawRowsCount (h : ℕ) := 3*h+(10*h+12)+3*(2*h+2)+2+h*(1+2*(1+2*(2*h+2)))

theorem rawRows_count (h ratio : ℕ) (ratio_ge : 2 ≤ ratio) :
    (rawRows h ratio ratio_ge).events.length ≤ rawRowsCount h := by
  have depth := StoredServe.gridDepth_count h ratio
  have Dbound := Runtime.gridDepth_bound h ratio ratio_ge
  have same := StoredServe.gridDepth_value h ratio ratio_ge
  simp only[rawRows,List.length_append,indexList_count,indexList_value,List.length_flatMap,
    List.length_cons,List.length_nil,List.length_finRange,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  simp only[Nat.zero_add,Nat.add_zero,Nat.reduceAdd,List.map_const',List.sum_replicate,List.length_finRange,nsmul_eq_mul]
  unfold rawRowsCount
  nlinarith

theorem filterIncluded_count {ratio : ℕ} (database : Core.RowDatabase h ratio n) (rows : List (Core.RawRow h ratio)) :
    (filterIncluded database rows).events.length ≤ 8*rows.length+1 := by
  induction rows with
  | nil => rfl
  | cons raw rest ih =>
    simp only[filterIncluded];split_ifs <;>
      simp only[Runtime.getRow,List.length_append,List.length_cons,List.length_nil] <;>omega

theorem includedRows_count {ratio : ℕ} (database : Core.RowDatabase h ratio n) (ratio_ge : 2 ≤ ratio) :
    (includedRows database ratio_ge).events.length ≤ rawRowsCount h+8*(2*h*(2*h+2))+1 := by
  have raw := rawRows_count h ratio ratio_ge
  have filter := filterIncluded_count database (rawRows h ratio ratio_ge).value
  have depth := Runtime.gridDepth_bound h ratio ratio_ge
  rw[rawRows_value,Core.rawRows_length] at filter
  have product := Nat.mul_le_mul_left (2*h) (show UpperBound.gridDepth h ratio+1 ≤ 2*h+2 by omega)
  simp only[includedRows,Traced.bind_events,List.length_append,rawRows_value]
  nlinarith

theorem words_flatMap {α : Type} (indices : List α) (f : α → List Event) (K : ℕ)
    (each : ∀ i ∈ indices, WordsWithin K (f i)) : WordsWithin K (indices.flatMap f) := by
  intro event member word present
  obtain ⟨i,member,found⟩ := List.mem_flatMap.mp member
  exact each i member event found word present

theorem rawRows_words (h ratio L : ℕ) (ratio_ge : 2 ≤ ratio) (ratio_width : ratio.size ≤ L) :
    WordsWithin (StoredServe.logarithmWordBudget h L+3*h+10) (rawRows h ratio ratio_ge).events := by
  let K := StoredServe.logarithmWordBudget h L+3*h+10
  have depth := Runtime.gridDepth_bound h ratio ratio_ge
  have same := StoredServe.gridDepth_value h ratio ratio_ge
  have di : (StoredServe.gridDepth h ratio).value+1 ≤ K := by dsimp[K];omega
  have hi : h ≤ K := by dsimp[K];omega
  have one : 1 ≤ K := by dsimp[K];omega
  have requests := indexList_words h K hi
  have depths := indexList_words ((StoredServe.gridDepth h ratio).value+1) K di
  have depth_trace := (StoredServe.gridDepth_words h ratio).mono (show StoredServe.logarithmWordBudget h ratio.size ≤ K by
    have product := Nat.mul_le_mul_right (2*h+4) (show 2*ratio.size+2*h+10 ≤ 2*L+2*h+10 by omega)
    dsimp[K,StoredServe.logarithmWordBudget] at *
    omega)
  have emitted : WordsWithin K ((List.finRange h).flatMap (fun i =>
      [⟨Operation.scan,[i.val.size]⟩]++([false,true] : List Bool).flatMap (fun _ =>
        [⟨Operation.scan,[1]⟩]++(List.finRange ((StoredServe.gridDepth h ratio).value+1)).flatMap (fun d =>
          [⟨Operation.scan,[d.val.size]⟩,⟨.cons,[i.val.size,1,d.val.size]⟩])))) := by
    apply words_flatMap
    intro i member
    have ii := ((Nat.size_le.mpr Nat.lt_two_pow_self : i.val.size ≤ i.val).trans (Nat.le_of_lt i.isLt)).trans hi
    rw [wordsWithin_append]
    refine ⟨?_,?_⟩
    · simpa[wordsWithin_cons] using ii
    · apply words_flatMap
      intro side member
      rw [wordsWithin_append]
      refine ⟨?_,?_⟩
      · simpa[wordsWithin_cons] using one
      · apply words_flatMap
        intro d member
        have dd := ((Nat.size_le.mpr Nat.lt_two_pow_self : d.val.size ≤ d.val).trans (Nat.le_of_lt d.isLt)).trans di
        simp only[wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
        exact ⟨dd,ii,one,dd⟩
  simp only[rawRows,indexList_value,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_singleton,forall_eq,and_true]
  exact ⟨⟨⟨⟨requests,depth_trace⟩,depths⟩,one,one⟩,emitted⟩

theorem filterIncluded_words {ratio : ℕ} (database : Core.RowDatabase h ratio n) (rows : List (Core.RawRow h ratio)) :
    WordsWithin (h+UpperBound.gridDepth h ratio+2) (filterIncluded database rows).events := by
  let K := h+UpperBound.gridDepth h ratio+2
  have one : 1 ≤ K := by dsimp[K];omega
  induction rows with
  | nil => simpa[filterIncluded,emit,wordsWithin_cons] using one
  | cons raw rest ih =>
    have ii : raw.1.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := raw.1.isLt;dsimp[K];omega)
    have dd : raw.2.2.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := raw.2.2.isLt;dsimp[K];omega)
    simp only[filterIncluded];split_ifs <;>
      simp only[Runtime.getRow,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
        or_false,forall_eq_or_imp,forall_eq,and_true] <;>aesop

theorem includedRows_words {ratio : ℕ} (database : Core.RowDatabase h ratio n) (L : ℕ)
    (ratio_ge : 2 ≤ ratio) (ratio_width : ratio.size ≤ L) :
    WordsWithin (StoredServe.logarithmWordBudget h L+3*h+10) (includedRows database ratio_ge).events := by
  have raw := rawRows_words h ratio L ratio_ge ratio_width
  have depth := Runtime.gridDepth_bound h ratio ratio_ge
  have filtered := (filterIncluded_words database (rawRows h ratio ratio_ge).value).mono
    (show h+UpperBound.gridDepth h ratio+2 ≤ StoredServe.logarithmWordBudget h L+3*h+10 by omega)
  simpa only[includedRows,Traced.bind_events,wordsWithin_append] using And.intro raw filtered

end BuyAtBulk.Computation.Runtime.StoredCore
