import BuyAtBulk.Computation.Runtime.OriginalSeed
import BuyAtBulk.Computation.PolynomialLP.BoxTrace

/-! The actual original initializer's repeated searches, finite scans, stored
unit openings and explicit failing index are fully traced. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.Computation.Runtime.Original
open BuyAtBulk.Computation.StoredOriginal
open OriginalPipeline Rational
variable {n resources requests : ℕ} (tables : Tables n resources requests)

private def seedFractional
    (entries : List (Entry (G:=tables.graphData.graph) tables.graphData.source tables.graphData.target))
    (returned : seedEntries tables (List.finRange requests)=some entries)
    (opening : Vector ℚ resources) (same : opening=Vector.replicate resources 1) : Fractional tables where
  opening := opening
  entries := entries
  opening_bounds := by intro a;simp [same]
  nonneg := by
    intro entry member
    rw [(seedEntries_indices tables _ entries returned).2 entry member]
    norm_num
  unit := seedEntries_unit tables entries returned
  capacity := by
    intro i a
    have nonneg : ∀ entry ∈ entries, 0  ≤  entry.2.1 := by
      intro entry member
      rw [(seedEntries_indices tables _ entries returned).2 entry member]
      norm_num
    have selected_nonneg := selectPaths_nonneg _ _ entries nonneg i
    calc
      _  ≤  ((selectPaths tables.graphData.source tables.graphData.target entries i).map Prod.fst).sum := by
        apply List.sum_le_sum
        intro entry member
        split
        · exact le_rfl
        · exact selected_nonneg entry member
      _ = 1 := seedEntries_unit tables entries returned i
      _ = opening[a.val] := by simp [same]

def initializeSeedTrace (zeros : Vector ℚ n) (same : zeros=Vector.replicate n 0) :
    Traced (Option (Fractional tables)) :=
  let indices := indexList requests
  let paths := seedEntriesTrace tables zeros indices.value
  match returned : paths.value with
  | none => ⟨none,indices.events++paths.events++[⟨.branch,[1]⟩,⟨.write,[1]⟩]⟩
  | some entries =>
    let opening := PolynomialLP.InputTrace.replicateTrace resources 1
    have source_return : seedEntries tables (List.finRange requests)=some entries := by
      simpa only [paths,indices,indexList_value,seedEntriesTrace_value tables zeros same] using returned
    let value := seedFractional tables entries source_return opening.value (by
      exact PolynomialLP.InputTrace.replicateTrace_value resources 1)
    ⟨some value,indices.events++paths.events++[⟨.branch,[1]⟩]++opening.events++[⟨.cons,[requests.size,resources.size]⟩,⟨.write,[1]⟩]⟩

theorem initializeSeedTrace_value (zeros : Vector ℚ n) (same : zeros=Vector.replicate n 0) :
    (initializeSeedTrace tables zeros same).value=initializeSeed tables := by
  unfold initializeSeedTrace
  dsimp only
  split
  · rename_i returned
    have source : seedEntries tables (List.finRange requests)=none := by
      simpa only [indexList_value,seedEntriesTrace_value tables zeros same] using returned
    unfold initializeSeed
    split
    · rfl
    · rename_i entries found
      cases source.symm.trans found
  · rename_i entries returned
    have source : seedEntries tables (List.finRange requests)=some entries := by
      simpa only [indexList_value,seedEntriesTrace_value tables zeros same] using returned
    unfold initializeSeed
    split
    · rename_i found
      cases source.symm.trans found
    · rename_i other found
      have equal := Option.some.inj (source.symm.trans found)
      subst other
      simp only [seedFractional,PolynomialLP.InputTrace.replicateTrace_value]

def initializationCount (n r h : ℕ) := (seedQueryCount n+9)*h+3*r+7

theorem initializeSeedTrace_count (zeros : Vector ℚ n) (same : zeros=Vector.replicate n 0) :
    (initializeSeedTrace tables zeros same).events.length ≤ initializationCount n resources requests := by
  have paths := seedEntriesTrace_count tables zeros (List.finRange requests)
  have opening := PolynomialLP.InputTrace.replicateTrace_count resources 1
  simp only [List.length_finRange] at paths
  unfold initializeSeedTrace
  dsimp only
  split <;> simp only [List.length_append,indexList_count,indexList_value,List.length_cons,List.length_nil]
  all_goals dsimp only [initializationCount];nlinarith

def initializationWords (n r h : ℕ) := seedWordBudget n h+r+h+10

theorem initializeSeedTrace_words (zeros : Vector ℚ n) (same : zeros=Vector.replicate n 0) :
    WordsWithin (initializationWords n resources requests) (initializeSeedTrace tables zeros same).events := by
  let K := initializationWords n resources requests
  have indices := indexList_words requests K (by dsimp [K,initializationWords];omega)
  have paths := (seedEntriesTrace_words tables zeros same (List.finRange requests)).mono
    (show _ ≤ K by dsimp [K,initializationWords];omega)
  have opening := (PolynomialLP.InputTrace.replicateTrace_words resources 1).mono
    (show _ ≤ K by norm_num [Code.ofRat,Code.bits];dsimp [K,initializationWords];omega)
  have one : 1 ≤ K := by dsimp [K,initializationWords];omega
  have ri : requests.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[K,initializationWords];omega)
  have ai : resources.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[K,initializationWords];omega)
  unfold initializeSeedTrace
  dsimp only
  split <;> simp only [indexList_value,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
    List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
  all_goals aesop

def initializeCheckedTrace : Traced (Except (Fin requests) (Fractional tables)) :=
  let zeros := seedZeros (n:=n)
  let initialized := initializeSeedTrace tables zeros.value (seedZeros_value (n:=n))
  match returned : initialized.value with
  | some fractional => ⟨.ok fractional,zeros.events++initialized.events++[⟨.branch,[1]⟩,⟨.write,[1]⟩]⟩
  | none =>
    let indices := indexList requests
    let missing := failedRequestTrace tables zeros.value indices.value
    have found : missing.value.isSome := by
      have source : initializeSeed tables=none := by
        simpa only [initialized,initializeSeedTrace_value] using returned
      rw [failedRequestTrace_value tables zeros.value (seedZeros_value (n:=n)),indexList_value]
      apply (failedRequest_isSome tables _).mpr
      apply (seedEntries_none_iff tables _).mpr
      obtain ⟨i,disconnected⟩ := (initializeSeed_none_iff tables).mp source
      exact ⟨i,List.mem_finRange i,disconnected⟩
    let index := missing.value.get found
    ⟨.error index,zeros.events++initialized.events++[⟨.branch,[1]⟩]++indices.events++missing.events++
      [⟨.branch,[1]⟩,⟨.write,[index.val.size]⟩]⟩

theorem initializeCheckedTrace_value : (initializeCheckedTrace tables).value=initializeChecked tables := by
  unfold initializeCheckedTrace
  dsimp only
  split
  · rename_i fractional returned
    have source : initializeSeed tables=some fractional := by
      simpa only [initializeSeedTrace_value] using returned
    unfold initializeChecked
    split
    · rename_i other found
      have equal := Option.some.inj (source.symm.trans found)
      subst other
      rfl
    · rename_i found
      cases source.symm.trans found
  · rename_i returned
    have source : initializeSeed tables=none := by
      simpa only [initializeSeedTrace_value] using returned
    unfold initializeChecked
    split
    · rename_i fractional found
      cases source.symm.trans found
    · simp only [failedRequestTrace_value tables _ (seedZeros_value (n:=n)),indexList_value]

def checkedInitializationCount (n r h : ℕ) := initializationCount n r h+(seedQueryCount n+6)*h+3*n+10

theorem initializeCheckedTrace_count : (initializeCheckedTrace tables).events.length ≤ checkedInitializationCount n resources requests := by
  have zeros := seedZeros_count (n:=n)
  have initialized := initializeSeedTrace_count tables (seedZeros (n:=n)).value (seedZeros_value (n:=n))
  have failed := failedRequestTrace_count tables (seedZeros (n:=n)).value (List.finRange requests)
  simp only [List.length_finRange] at failed
  unfold initializeCheckedTrace
  dsimp only
  split <;> simp only [List.length_append,List.length_cons,List.length_nil,indexList_count,indexList_value]
  all_goals dsimp only [checkedInitializationCount];nlinarith

theorem initializeCheckedTrace_words :
    WordsWithin (initializationWords n resources requests) (initializeCheckedTrace tables).events := by
  let K := initializationWords n resources requests
  have zeros := seedZeros_words (n:=n) K (by dsimp [K,initializationWords,seedWordBudget];omega)
  have initialized := initializeSeedTrace_words tables (seedZeros (n:=n)).value (seedZeros_value (n:=n))
  have failed := (failedRequestTrace_words tables (seedZeros (n:=n)).value (seedZeros_value (n:=n))
    (List.finRange requests)).mono (show _ ≤ K by dsimp[K,initializationWords];omega)
  have indices := indexList_words requests K (by dsimp[K,initializationWords];omega)
  have one : 1 ≤ K := by dsimp[K,initializationWords];omega
  have anyIndex (i : Fin requests) : i.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans
    (by have := i.isLt;dsimp[K,initializationWords];omega)
  unfold initializeCheckedTrace
  dsimp only
  split <;> simp only [indexList_value,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
    List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
  all_goals aesop

end BuyAtBulk.Computation.Runtime.Original
