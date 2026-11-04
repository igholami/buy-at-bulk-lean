import BuyAtBulk.Computation.PolynomialLP.CompactEncoding
import BuyAtBulk.Computation.Runtime.Weights
import BuyAtBulk.Computation.FlowDecomposition.Algorithm

/-! Stored optimizer-coordinate reads use explicit arithmetic index schedules;
no path code, finite-enumeration inverse or callback enters the decoder. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace BuyAtBulk.Computation.Runtime.CompactDecode
open Rational BuyAtBulk.PolynomialLP.CompactEncoding
variable {n h : ℕ}

def addIndex (a b : ℕ) : Traced ℕ := emit .natAdd [a.size,b.size,(a+b).size] (a+b)
def mulIndex (a b : ℕ) : Traced ℕ := emit .natMul [a.size,b.size,(a*b).size] (a*b)
@[simp] theorem addIndex_value (a b : ℕ) : (addIndex a b).value=a+b := rfl
@[simp] theorem mulIndex_value (a b : ℕ) : (mulIndex a b).value=a*b := rfl
@[simp] theorem addIndex_count (a b : ℕ) : (addIndex a b).events.length=1 := rfl
@[simp] theorem mulIndex_count (a b : ℕ) : (mulIndex a b).events.length=1 := rfl

@[simp] theorem openingIndex (v : Fin n) : (variableEquiv n h (Sum.inl v)).val=v.val := rfl
@[simp] theorem nodeIndex (i : Fin h) (v : Fin n) :
    (variableEquiv n h (Sum.inr (Sum.inl (i,v)))).val=n+(i.val*n+v.val) := by
  change n+(v.val+n*i.val)=_
  ring
@[simp] theorem transportIndex (i : Fin h) (u v : Fin n) :
    (variableEquiv n h (Sum.inr (Sum.inr (i,u,v)))).val=n+(h*n+(i.val*(n*n)+(u.val*n+v.val))) := by
  change n+(h*n+(v.val+n*u.val+n*n*i.val))=_
  ring

def readOpening (point : Vector ℚ (variableCount n h)) (v : Fin n) : Traced ℚ :=
  readRat point (variableEquiv n h (.inl v))
@[simp] theorem readOpening_value (point : Vector ℚ (variableCount n h)) (v : Fin n) :
    (readOpening point v).value=point[(variableEquiv n h (.inl v)).val] := rfl
@[simp] theorem readOpening_count (point : Vector ℚ (variableCount n h)) (v : Fin n) :
    (readOpening point v).events.length=1 := rfl

def readTransport (point : Vector ℚ (variableCount n h)) (i : Fin h) (u v : Fin n) : Traced ℚ :=
  let square := mulIndex n n
  let nodes := mulIndex h n
  let offset := addIndex n nodes.value
  let commodity := mulIndex i.val square.value
  let row := mulIndex u.val n
  let pair := addIndex row.value v.val
  let arc := addIndex commodity.value pair.value
  let finalIndex := addIndex offset.value arc.value
  have index_bound : finalIndex.value<variableCount n h := by
    have source := (variableEquiv n h (.inr (.inr (i,u,v)))).isLt
    rw [transportIndex] at source
    simpa only [finalIndex,offset,nodes,square,commodity,row,pair,arc,addIndex_value,mulIndex_value,Nat.add_assoc] using source
  let result := readRat point ⟨finalIndex.value,index_bound⟩
  ⟨result.value,square.events++nodes.events++offset.events++commodity.events++row.events++pair.events++arc.events++finalIndex.events++result.events⟩

@[simp] theorem readTransport_value (point : Vector ℚ (variableCount n h)) (i : Fin h) (u v : Fin n) :
    (readTransport point i u v).value=point[(variableEquiv n h (.inr (.inr (i,u,v)))).val] := by
  simp only [readTransport,readRat,emit_value,addIndex_value,mulIndex_value,transportIndex]
  congr 1
  omega
@[simp] theorem readTransport_count (point : Vector ℚ (variableCount n h)) (i : Fin h) (u v : Fin n) :
    (readTransport point i u v).events.length=9 := by
  simp only [readTransport,List.length_append,addIndex_count,mulIndex_count,readRat,emit_length]

def opening (point : Vector ℚ (variableCount n h)) : Traced (Vector ℚ n) :=
  Weights.materialize (readOpening point) (fun q=>(Code.ofRat q).bits)
@[simp] theorem opening_value (point : Vector ℚ (variableCount n h)) (v : Fin n) :
    (opening point).value[v.val]=point[(variableEquiv n h (.inl v)).val] := by
  simp only [opening,Weights.materialize_get,readOpening_value]
theorem opening_count (point : Vector ℚ (variableCount n h)) : (opening point).events.length ≤ 3*n+1 := by
  simpa only [opening,Nat.mul_comm] using Weights.materialize_count (readOpening point) (fun q=>(Code.ofRat q).bits) 1 (by intro v;rfl)

def transportMatrix (point : Vector ℚ (variableCount n h)) (i : Fin h) :
    Traced (FlowDecomposition.FlowMatrix n) :=
  Weights.materialize (fun u=>Weights.materialize (readTransport point i u) (fun q=>(Code.ofRat q).bits)) (fun _=>n.size)
@[simp] theorem transportMatrix_value (point : Vector ℚ (variableCount n h)) (i : Fin h) (u v : Fin n) :
    (transportMatrix point i).value[u.val][v.val]=point[(variableEquiv n h (.inr (.inr (i,u,v)))).val] := by
  simp only [transportMatrix,Weights.materialize_get,readTransport_value]
theorem transportMatrix_count (point : Vector ℚ (variableCount n h)) (i : Fin h) :
    (transportMatrix point i).events.length ≤ 11*n^2+3*n+1 := by
  have row (u : Fin n) := Weights.materialize_count (readTransport point i u) (fun q=>(Code.ofRat q).bits) 9 (by intro v;simp)
  have all := Weights.materialize_count (fun u=>Weights.materialize (readTransport point i u) (fun q=>(Code.ofRat q).bits)) (fun _=>n.size) (n*11+1) row
  dsimp only [transportMatrix]
  nlinarith

def indexWordBudget (n h L : ℕ) := variableCount n h+n*n+n+h+L+10

theorem readOpening_words (point : Vector ℚ (variableCount n h)) (v : Fin n) (L : ℕ)
    (inputs : ∀ j : Fin (variableCount n h),(Code.ofRat point[j.val]).bits ≤ L) :
    WordsWithin (indexWordBudget n h L) (readOpening point v).events := by
  have index : v.val.size ≤ indexWordBudget n h L := (Nat.size_le.mpr Nat.lt_two_pow_self).trans
    (by have := v.isLt;dsimp[indexWordBudget];omega)
  have value := inputs (variableEquiv n h (.inl v))
  simp only [readOpening,readRat,emit,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
    or_false,forall_eq_or_imp,forall_eq,and_true,openingIndex]
  exact ⟨index,value.trans (by dsimp[indexWordBudget];omega)⟩

theorem readTransport_words (point : Vector ℚ (variableCount n h)) (i : Fin h) (u v : Fin n) (L : ℕ)
    (inputs : ∀ j : Fin (variableCount n h),(Code.ofRat point[j.val]).bits ≤ L) :
    WordsWithin (indexWordBudget n h L) (readTransport point i u v).events := by
  let K := indexWordBudget n h L
  have final := (variableEquiv n h (.inr (.inr (i,u,v)))).isLt
  rw [transportIndex] at final
  have value := inputs (⟨(n+h*n)+(i.val*(n*n)+(u.val*n+v.val)),by omega⟩ : Fin (variableCount n h))
  simp only [Nat.add_assoc] at value
  have size (a : ℕ) (bound : a ≤ K) : a.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans bound
  have ib := i.isLt
  have ub := u.isLt
  have vb := v.isLt
  simp only [readTransport,addIndex,mulIndex,readRat,emit,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
    List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true,Nat.add_assoc]
  repeat' apply And.intro
  all_goals first
    | exact value.trans (by dsimp[K,indexWordBudget];omega)
    | apply size;dsimp[K,indexWordBudget];omega

theorem opening_words (point : Vector ℚ (variableCount n h)) (L : ℕ)
    (inputs : ∀ j : Fin (variableCount n h),(Code.ofRat point[j.val]).bits ≤ L) :
    WordsWithin (indexWordBudget n h L) (opening point).events := by
  apply Weights.materialize_words
  · dsimp[indexWordBudget];omega
  · exact fun v=>readOpening_words point v L inputs
  · intro v
    rw [readOpening_value]
    exact (inputs _).trans (by dsimp[indexWordBudget];omega)

theorem transportMatrix_words (point : Vector ℚ (variableCount n h)) (i : Fin h) (L : ℕ)
    (inputs : ∀ j : Fin (variableCount n h),(Code.ofRat point[j.val]).bits ≤ L) :
    WordsWithin (indexWordBudget n h L) (transportMatrix point i).events := by
  apply Weights.materialize_words
  · dsimp[indexWordBudget];omega
  · intro u
    apply Weights.materialize_words
    · dsimp[indexWordBudget];omega
    · exact fun v=>readTransport_words point i u v L inputs
    · intro v
      rw [readTransport_value]
      exact (inputs _).trans (by dsimp[indexWordBudget];omega)
  · intro u
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[indexWordBudget];omega)

end BuyAtBulk.Computation.Runtime.CompactDecode
