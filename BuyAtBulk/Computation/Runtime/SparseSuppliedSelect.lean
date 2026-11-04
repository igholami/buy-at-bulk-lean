import BuyAtBulk.Computation.Runtime.SparseSuppliedAggregation
import BuyAtBulk.Computation.StoredOriginal.Paths

/-! Instrumented dependent request filtering. Paths are immutable references;
copying a selected list cell stores its rational weight and path reference. -/
set_option maxHeartbeats 1800000
namespace BuyAtBulk.Computation.Runtime.SparseSupplied
open Rational StoredOriginal
variable {n h : ℕ} {G : SimpleGraph (Fin n)} (source target : Fin h → Fin n)

def select (i : Fin h) : List (Entry (G:=G) source target) →
    Traced (FlowDecomposition.WeightedPaths G (source i) (target i))
  | [] => ⟨[],[⟨.branch,[1]⟩]⟩
  | e::rest =>
    let tail := select i rest
    let initial : List Event := [⟨.branch,[1]⟩,⟨.scan,[1]⟩,
      ⟨.natCompare,[e.1.val.size,i.val.size]⟩,⟨.branch,[1]⟩]
    if same : e.1=i then
      ⟨(same ▸ e.2)::tail.value,initial++tail.events++
        [⟨.cons,[(Code.ofRat e.2.1).bits,n.size]⟩]⟩
    else ⟨tail.value,initial++tail.events⟩

@[simp] theorem select_value (i : Fin h) (entries : List (Entry (G:=G) source target)) :
    (select source target i entries).value=selectPaths source target entries i := by
  induction entries with
  | nil => rfl
  | cons e rest ih =>
    simp only [select,selectPaths,List.filterMap_cons]
    split_ifs <;> simp_all [selectPaths]

theorem select_count (i : Fin h) (entries : List (Entry (G:=G) source target)) :
    (select source target i entries).events.length ≤ 5*entries.length+1 := by
  induction entries with
  | nil => simp [select]
  | cons e rest ih =>
    simp only [select]
    split_ifs <;> simp only [List.length_append,List.length_cons,List.length_nil] <;> omega

theorem selected_bits (i : Fin h) (entries : List (Entry (G:=G) source target)) (L : ℕ)
    (bits : ∀ e∈entries,(Code.ofRat e.2.1).bits ≤ L) :
    ∀ e∈selectPaths source target entries i,(Code.ofRat e.1).bits ≤ L := by
  intro e mem
  obtain ⟨⟨j,w,p⟩,member,selected⟩ := List.mem_filterMap.mp mem
  dsimp only at selected
  split_ifs at selected with same
  · subst j
    simp only [Option.some.injEq] at selected
    subst e
    exact bits _ member

theorem select_words (i : Fin h) (entries : List (Entry (G:=G) source target)) (L : ℕ)
    (bits : ∀ e∈entries,(Code.ofRat e.2.1).bits ≤ L) :
    WordsWithin (n+h+L+1) (select source target i entries).events := by
  have one : 1 ≤ n+h+L+1 := by omega
  have ni : n.size ≤ n+h+L+1 := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have idx (j : Fin h) : j.val.size ≤ n+h+L+1 :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  induction entries with
  | nil => simp[select,WordsWithin,one]
  | cons e rest ih =>
    have tail := ih (fun e mem=>bits e (by simp[mem]))
    have eb : (Code.ofRat e.2.1).bits ≤ n+h+L+1 := (bits e (by simp)).trans (by omega)
    simp only [select]
    split_ifs <;> simp [wordsWithin_append,wordsWithin_cons,one,idx,ni,tail,eb]

end BuyAtBulk.Computation.Runtime.SparseSupplied
