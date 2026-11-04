import BuyAtBulk.Computation.Runtime.PhaseMetadataWords
import BuyAtBulk.Computation.Runtime.ArrayDot
import BuyAtBulk.Computation.Runtime.FreeRoutes

namespace BuyAtBulk.Computation.Runtime.StoredRounding
open BuyAtBulk.UpperBound
open Rational
variable {n h : ℕ}

theorem activeFlags_zeroSet (lengths : Vector ℚ h) :
    StoredState.boughtSet (activeFlags lengths false).value=Rounding.zeroActive (fun i => lengths[i.val]) := by
  ext i
  simp only[StoredState.mem_boughtSet,activeFlags_get,Bool.false_eq_true,ite_false,Rounding.zeroActive,Finset.mem_filter,
    Finset.mem_univ,true_and]
  by_cases zero : lengths[i.val]=0 <;>simp_all

theorem activeFlags_positiveSet (lengths : Vector ℚ h) :
    StoredState.boughtSet (activeFlags lengths true).value=Rounding.positiveActive (fun i => lengths[i.val]) := by
  ext i
  simp only[StoredState.mem_boughtSet,activeFlags_get,ite_true,Rounding.positiveActive,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases zero : lengths[i.val]=0 <;>simp_all

@[simp] theorem constantFalse_set (m : ℕ) : StoredState.boughtSet (constantVector m false 1).value=∅ := by
  ext i
  simp[StoredState.mem_boughtSet]


def activeEmpty (active : Vector Bool h) : Traced Bool :=
  let indices := indexList h
  let selected := StoredCore.filterActive active indices.value
  ⟨selected.value.isEmpty,indices.events++selected.events++[⟨.branch,[1]⟩]⟩

@[simp] theorem activeEmpty_value (active : Vector Bool h) :
    (activeEmpty active).value=decide (StoredState.boughtSet active=∅) := by
  simp only[activeEmpty,indexList_value,StoredCore.filterActive_value]
  apply Bool.eq_iff_iff.mpr
  simp only[List.isEmpty_iff,decide_eq_true_eq]
  constructor
  · intro empty
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i member
    have present : i ∈ (List.finRange h).filter (fun i => active[i.val]) := by
      simp only[List.mem_filter,List.mem_finRange,true_and]
      exact (StoredState.mem_boughtSet active i).mp member
    simpa [empty] using present
  · intro empty
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro i member
    have bought : i ∈ StoredState.boughtSet active := by
      apply (StoredState.mem_boughtSet active i).mpr
      exact (List.mem_filter.mp member).2
    simpa [empty] using bought

theorem activeEmpty_count (active : Vector Bool h) :
    (activeEmpty active).events.length ≤ 7*h+2 := by
  have count := StoredCore.filterActive_count active (List.finRange h)
  simp only[List.length_finRange] at count
  simp only[activeEmpty,indexList_value,indexList_count,List.length_append,List.length_cons,List.length_nil]
  omega

theorem activeEmpty_words (active : Vector Bool h) :
    WordsWithin (h+1) (activeEmpty active).events := by
  have indices := indexList_words h (h+1) (by omega)
  have selected := StoredCore.filterActive_words active (List.finRange h)
  simpa only[activeEmpty,indexList_value,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
    List.mem_singleton,forall_eq,and_true] using And.intro (And.intro indices selected) (show 1≤h+1 by omega)

def restrictedCell (physical buying opening : Vector ℚ n) (v : Fin n) : Traced ℚ := do
  let p ← readRat physical v
  let zero ← zeroTest p
  let zero ← branch zero
  if zero then readRat opening v else emit .write [3] 0

def restrictedOpening (physical buying opening : Vector ℚ n) : Traced (Vector ℚ n) :=
  Weights.materialize (restrictedCell physical buying opening) (fun q => (Code.ofRat q).bits)

@[simp] theorem restrictedOpening_get (physical buying opening : Vector ℚ n) (v : Fin n) :
    (restrictedOpening physical buying opening).value[v.val]=
      Rounding.restrictedOpening (fun v => buying[v.val]) (fun v => physical[v.val]) (fun v => opening[v.val]) v := by
  by_cases hp : physical[v.val]=0 <;> by_cases hb : buying[v.val]=0 <;>
    simp [restrictedOpening,Weights.materialize_get,restrictedCell,raisedCell,readRat,zeroTest,branch,
      Rounding.restrictedOpening,Rounding.raisedOpening,hp,hb]

def maskCell (physical : Vector ℚ n) (bought : Vector Bool n) (v : Fin n) : Traced Bool := do
  let p ← readRat physical v
  let zero ← zeroTest p
  let old ← emit .read [v.val.size,1] bought[v.val]
  emit .branch [1] (old && zero)

def maskBought (physical : Vector ℚ n) (bought : Vector Bool n) : Traced (Vector Bool n) :=
  Weights.materialize (maskCell physical bought) (fun _ => 1)

@[simp] theorem maskBought_get (physical : Vector ℚ n) (bought : Vector Bool n) (v : Fin n) :
    (maskBought physical bought).value[v.val]=(bought[v.val] && decide (physical[v.val]=0)) := by
  simp [maskBought,Weights.materialize_get,maskCell,readRat,zeroTest]
  rfl

@[simp] theorem maskBought_set (physical : Vector ℚ n) (bought : Vector Bool n) :
    StoredState.boughtSet (maskBought physical bought).value=
      (StoredState.boughtSet bought).filter (fun v => physical[v.val]=0) := by
  ext v
  simp [StoredState.mem_boughtSet]

theorem restrictedOpening_count (physical buying opening : Vector ℚ n) :
    (restrictedOpening physical buying opening).events.length ≤ 9*n+1 := by
  have per (v : Fin n) : (restrictedCell physical buying opening v).events.length ≤ 7 := by
    by_cases hp : physical[v.val]=0 <;> by_cases hb : buying[v.val]=0 <;>
      simp [restrictedCell,raisedCell,Traced.bind_events,readRat,emit,zeroTest,branch,hp,hb]
  simpa only[restrictedOpening,Nat.reduceAdd,Nat.mul_comm] using
    Weights.materialize_count (restrictedCell physical buying opening) (fun q => (Code.ofRat q).bits) 7 per

theorem maskBought_count (physical : Vector ℚ n) (bought : Vector Bool n) :
    (maskBought physical bought).events.length ≤ 6*n+1 := by
  simpa only[maskBought,Nat.reduceAdd,Nat.mul_comm] using
    Weights.materialize_count (maskCell physical bought) (fun _ => 1) 4 (by intro;rfl)

theorem restrictedOpening_bits (physical buying opening : Vector ℚ n) (L : ℕ) (constant : 4 ≤ L)
    (inputs : ∀ v : Fin n,(Code.ofRat opening[v.val]).bits ≤ L) (v : Fin n) :
    (Code.ofRat (restrictedOpening physical buying opening).value[v.val]).bits ≤ L := by
  rw [restrictedOpening_get]
  unfold Rounding.restrictedOpening
  split_ifs
  · exact inputs v
  · have literal : (Code.ofRat 0).bits=3 := by decide
    rw [literal];omega

theorem restrictedOpening_words (physical buying opening : Vector ℚ n) (L : ℕ) (constant : 4 ≤ L)
    (pw : ∀ v : Fin n,(Code.ofRat physical[v.val]).bits ≤ L)
    (bw : ∀ v : Fin n,(Code.ofRat buying[v.val]).bits ≤ L)
    (ow : ∀ v : Fin n,(Code.ofRat opening[v.val]).bits ≤ L) :
    WordsWithin (n+L+5) (restrictedOpening physical buying opening).events := by
  let K := n+L+5
  apply Weights.materialize_words _ _ K (by dsimp[K];omega)
  · intro v
    have vi : v.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := v.isLt;dsimp[K];omega)
    have p := pw v
    have b := bw v
    have o := ow v
    by_cases hp : physical[v.val]=0 <;> by_cases hb : buying[v.val]=0 <;>
      simp only[restrictedCell,raisedCell,Traced.bind_events,Traced.bind_value,readRat,emit_value,zeroTest,branch,hp,hb,
        decide_true,decide_false,Bool.false_eq_true,ite_true,ite_false,wordsWithin_append,emit,wordsWithin_cons,
        wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
    all_goals norm_num [Code.ofRat,Code.bits] at *;dsimp[K] at *;omega
  · intro v
    have actual := restrictedOpening_bits physical buying opening L constant ow v
    simpa only[restrictedOpening,Weights.materialize_get] using actual.trans (show L ≤ K by dsimp[K];omega)

theorem maskBought_words (physical : Vector ℚ n) (bought : Vector Bool n) (L : ℕ)
    (pw : ∀ v : Fin n,(Code.ofRat physical[v.val]).bits ≤ L) :
    WordsWithin (n+L+5) (maskBought physical bought).events := by
  let K := n+L+5
  apply Weights.materialize_words _ _ K (by dsimp[K];omega)
  · intro v
    have vi : v.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := v.isLt;dsimp[K];omega)
    have p := pw v
    simp only[maskCell,Traced.bind_events,Traced.bind_value,readRat,emit_value,zeroTest,
      wordsWithin_append,emit,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
      or_false,forall_eq_or_imp,forall_eq,and_true]
    dsimp[K] at *
    omega
  · intro v
    dsimp[K];omega

end BuyAtBulk.Computation.Runtime.StoredRounding
