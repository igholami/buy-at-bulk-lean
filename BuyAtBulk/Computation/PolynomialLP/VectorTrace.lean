import BuyAtBulk.Computation.PolynomialLP.Optimization
import BuyAtBulk.Computation.Runtime.Weights

/-! List-to-vector conversion charges each actual prefix traversal. The source
uses list indexing inside Vector.ofFn; no constant-time list access is assumed. -/
set_option maxHeartbeats 2000000
namespace BuyAtBulk.PolynomialLP
open Computation Computation.Runtime Rational

def valueListLength : List ℚ → Traced ℕ
  | [] => emit .write [1] 0
  | _::rest =>
    let tail := valueListLength rest
    ⟨tail.value+1,⟨.scan,[1]⟩::tail.events++[⟨.natAdd,[tail.value.size,1,(tail.value+1).size]⟩]⟩

@[simp] theorem valueListLength_value (values : List ℚ) :
    (valueListLength values).value=values.length := by
  induction values <;> simp_all [valueListLength]

@[simp] theorem valueListLength_count (values : List ℚ) :
    (valueListLength values).events.length=2*values.length+1 := by
  induction values <;> simp_all [valueListLength,emit] <;> omega

theorem valueListLength_words (values : List ℚ) (W : ℕ) (bound : values.length+2≤W) :
    WordsWithin W (valueListLength values).events := by
  induction values with
  | nil => simp [valueListLength,emit,WordsWithin]; omega
  | cons q rest ih =>
    have previous := ih (by simpa only [List.length_cons] using (show rest.length+2≤W by simp only [List.length_cons] at bound; omega))
    have a : rest.length.size≤W := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by simp only [List.length_cons] at bound; omega)
    have b : (rest.length+1).size≤W := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by simp only [List.length_cons] at bound; omega)
    simpa only [valueListLength,valueListLength_value,wordsWithin_cons,wordsWithin_append,
      wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true] using
      And.intro (And.intro (by omega : 1≤W) previous) (And.intro a (And.intro (by omega : 1≤W) b))

def listReadTrace : List ℚ → ℕ → Traced ℚ
  | [],_ => emit .branch [1] 0
  | q::_,0 => ⟨q,[⟨.scan,[1]⟩,⟨.branch,[1]⟩,⟨.read,[(Code.ofRat q).bits]⟩]⟩
  | _::rest,index+1 =>
    let tail := listReadTrace rest index
    ⟨tail.value,[⟨.scan,[1]⟩,⟨.branch,[1]⟩,⟨.natSub,[(index+1).size,1,index.size]⟩]++tail.events⟩

@[simp] theorem listReadTrace_value (values : List ℚ) (i : ℕ) (valid : i<values.length) :
    (listReadTrace values i).value=values[i] := by
  induction values generalizing i with
  | nil => simp at valid
  | cons q rest ih =>
    cases i with
    | zero => rfl
    | succ i => simpa only [listReadTrace,List.getElem_cons_succ] using ih i (by simpa using valid)

theorem listReadTrace_count (values : List ℚ) (i : ℕ) :
    (listReadTrace values i).events.length≤3*(i+1)+1 := by
  induction values generalizing i with
  | nil => simp [listReadTrace]
  | cons q rest ih =>
    cases i with
    | zero => simp [listReadTrace]
    | succ i => have next := ih i; simp only [listReadTrace,List.length_append,List.length_cons,List.length_nil]; omega

theorem listReadTrace_words (values : List ℚ) (i W : ℕ) (index : i+2≤W)
    (cells : ∀ q∈values,(Code.ofRat q).bits≤W) : WordsWithin W (listReadTrace values i).events := by
  induction values generalizing i with
  | nil => simp [listReadTrace,emit,WordsWithin]; omega
  | cons q rest ih =>
    cases i with
    | zero =>
      have scalar := cells q (by simp)
      simp only [listReadTrace,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
        or_false,forall_eq_or_imp,forall_eq,and_true]
      exact ⟨by omega,by omega,scalar⟩
    | succ i =>
      have next := ih i (by omega) (fun q member => cells q (by simp [member]))
      have a : i.size≤W := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
      have b : (i+1).size≤W := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
      simpa only [listReadTrace,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,
        List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true] using
        And.intro (And.intro (by omega : 1≤W) (And.intro (by omega : 1≤W)
          (And.intro b (And.intro (by omega : 1≤W) a)))) next

def vectorFromListTrace (values : List ℚ) (n : ℕ) : Traced (Option (Vector ℚ n)) :=
  let length := valueListLength values
  if length.value=n then
    let vector := Weights.materialize (fun i : Fin n => listReadTrace values i.val) (fun q => (Code.ofRat q).bits)
    ⟨some vector.value,length.events++[⟨.natCompare,[length.value.size,n.size]⟩,⟨.branch,[1]⟩]++vector.events⟩
  else ⟨none,length.events++[⟨.natCompare,[length.value.size,n.size]⟩,⟨.branch,[1]⟩]⟩

@[simp] theorem vectorFromListTrace_value (values : List ℚ) (n : ℕ) :
    (vectorFromListTrace values n).value=vectorFromList values n := by
  unfold vectorFromListTrace vectorFromList
  simp only [valueListLength_value]
  split_ifs with length
  · change some (Weights.materialize (fun i : Fin n => listReadTrace values i.val) (fun q => (Code.ofRat q).bits)).value = some _
    apply congrArg some
    apply Vector.ext
    intro i hi
    simpa [Weights.materialize] using listReadTrace_value values i (by omega)
  · rfl

def vectorFromListCount (n : ℕ) := 2*n+3+n*(3*n+6)+1

theorem vectorFromListTrace_count (values : List ℚ) (n : ℕ) (length : values.length=n) :
    (vectorFromListTrace values n).events.length≤vectorFromListCount n := by
  have materialized := Weights.materialize_count (fun i : Fin n => listReadTrace values i.val)
    (fun q => (Code.ofRat q).bits) (3*n+4) (fun i => (listReadTrace_count values i.val).trans (by have := i.isLt; omega))
  simp only [vectorFromListTrace,valueListLength_value,length,ite_true,List.length_append,
    valueListLength_count,List.length_cons,List.length_nil]
  dsimp only [vectorFromListCount]
  nlinarith

theorem vectorFromListTrace_words (values : List ℚ) (n W : ℕ) (length : values.length=n)
    (indices : n+2≤W) (cells : ∀ q∈values,(Code.ofRat q).bits≤W) :
    WordsWithin W (vectorFromListTrace values n).events := by
  have counted := valueListLength_words values W (by omega)
  have materialized := Weights.materialize_words (fun i : Fin n => listReadTrace values i.val)
    (fun q => (Code.ofRat q).bits) W (by omega)
    (fun i => listReadTrace_words values i.val W (by have := i.isLt; omega) cells)
    (fun i => by rw [listReadTrace_value values i.val (by omega)]; exact cells _ (List.getElem_mem _))
  have size : n.size≤W := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  simpa only [vectorFromListTrace,valueListLength_value,length,ite_true,wordsWithin_append,
    wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,
    forall_eq,and_true] using And.intro (And.intro counted (And.intro (And.intro size size) (by omega : 1≤W))) materialized
end BuyAtBulk.PolynomialLP
