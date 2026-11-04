import BuyAtBulk.Computation.Runtime.CompactLift

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.Computation.Runtime.CompactLift
open Rational BuyAtBulk.PolynomialLP.CompactEncoding
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

def commodityWords (n h L : ℕ) := CompactDecode.indexWordBudget n h L+FlowExtract.decompositionWords n L+
  WeightedLength.wordBudget n (n*n+1) L (2*n*n*L+4)+WeightedLength.outputBudget n (n*n+1) L (2*n*n*L+4)+n+h+L+20

def allowanceBits (n L : ℕ) := WeightedLength.outputBudget n (n*n+1) L (2*n*n*L+4)

theorem entries_bits (f : CompactFlow.Solution input.graph h) (point : Vector ℚ (variableCount n h))
    (coordinates : f.coordinates=decode (fun j=>point[j.val])) (i : Fin h) (L : ℕ)
    (pointBits : ∀ j : Fin (variableCount n h),(Code.ofRat point[j.val]).bits+1 ≤ L) :
    ∀ e∈FlowDecomposition.entries input.graph (Equiv.refl _) f i,(Code.ofRat e.1).bits ≤ 2*n*n*L+4 := by
  have matrixEq := transportMatrix_eq input f point coordinates i
  have matrixBits (u v : Fin n) : (Code.ofRat (CompactDecode.transportMatrix point i).value[u.val][v.val]).bits ≤ L := by
    rw [CompactDecode.transportMatrix_value]
    have bound := pointBits (variableEquiv n h (.inr (.inr (i,u,v))))
    omega
  have denom := FlowExtract.denominatorBits_bound (CompactDecode.transportMatrix point i).value L matrixBits
  intro e member
  have bound := ((FlowDecomposition.entries_verified input.graph (Equiv.refl _) f i).weight_words e member).2.2
  rw [←matrixEq] at bound
  nlinarith

theorem fractionalLength_bits (f : CompactFlow.Solution input.graph h) (point : Vector ℚ (variableCount n h))
    (coordinates : f.coordinates=decode (fun j=>point[j.val])) (i : Fin h) (L : ℕ) (constant : 5 ≤ L)
    (pointBits : ∀ j : Fin (variableCount n h),(Code.ofRat point[j.val]).bits+1 ≤ L)
    (physicalBits : ∀ v : Fin n,(Code.ofRat (f.physical v)).bits+1 ≤ L) :
    (Code.ofRat (FlowDecomposition.fractionalLength input.graph (Equiv.refl _) f i)).bits ≤ allowanceBits n L := by
  have weights := entries_bits input f point coordinates i L pointBits
  have bound := WeightedLength.run_bits (Vector.ofFn f.physical) (FlowDecomposition.entries input.graph (Equiv.refl _) f i)
    L (2*n*n*L+4) constant (by simpa only [Vector.getElem_ofFn] using physicalBits) weights
  have value : (WeightedLength.run (Vector.ofFn f.physical) (FlowDecomposition.entries input.graph (Equiv.refl _) f i)).value=
      FlowDecomposition.fractionalLength input.graph (Equiv.refl _) f i := by
    simp only [WeightedLength.run_value,FlowDecomposition.fractionalLength,Vector.getElem_ofFn,Fin.eta]
  rw [value] at bound
  apply bound.trans
  dsimp only [WeightedLength.outputBudget,allowanceBits]
  gcongr
  exact (FlowDecomposition.entries_verified input.graph (Equiv.refl _) f i).sparse

theorem commodity_words (f : CompactFlow.Solution input.graph h) (point : Vector ℚ (variableCount n h))
    (coordinates : f.coordinates=decode (fun j=>point[j.val])) (i : Fin h) (L : ℕ) (constant : 5 ≤ L)
    (pointBits : ∀ j : Fin (variableCount n h),(Code.ofRat point[j.val]).bits+1 ≤ L)
    (physicalBits : ∀ v : Fin n,(Code.ofRat (f.physical v)).bits+1 ≤ L) :
    WordsWithin (commodityWords n h L)
      (commodity input (Vector.ofFn f.physical) (Vector.ofFn f.source) (Vector.ofFn f.target) point i).events := by
  let K := commodityWords n h L
  let matrix := (CompactDecode.transportMatrix point i).value
  let entries := FlowDecomposition.entries input.graph (Equiv.refl _) f i
  have matrixEq := transportMatrix_eq input f point coordinates i
  have matrixValues (u v : Fin n) : matrix[u.val][v.val]=f.transport i u v := by
    simp only [matrix,matrixEq,FlowDecomposition.storedMatrix,Vector.getElem_ofFn,Equiv.refl_symm,Equiv.refl_apply]
  have matrixBits (u v : Fin n) : (Code.ofRat matrix[u.val][v.val]).bits ≤ L := by
    dsimp only [matrix]
    rw [CompactDecode.transportMatrix_value]
    have bound := pointBits (variableEquiv n h (.inr (.inr (i,u,v))))
    omega
  have decoded := (CompactDecode.transportMatrix_words point i L (by intro j;have bound:=pointBits j;omega)).mono
    (show _ ≤ K by dsimp[K,commodityWords];omega)
  have search := (FlowExtract.decompose_words input matrix (f.source i) (f.target i) L matrixBits
    (by intro u v;rw[matrixValues];exact f.transport_nonneg i u v)
    (by intro u v;rw[matrixValues];exact f.transport_le_one i u v)
    (by intro u v missing;rw[matrixValues];exact f.transport_nonedge i u v missing)
    (by intro v;simp only [matrixValues];have incoming:=f.incoming_balance i v;have outgoing:=f.outgoing_balance i v;split_ifs at incoming outgoing ⊢ <;> simp_all <;> linarith)).mono
      (show _ ≤ K by dsimp[K,commodityWords];omega)
  have verified := FlowDecomposition.entries_verified input.graph (Equiv.refl _) f i
  have denom := FlowExtract.denominatorBits_bound matrix L matrixBits
  have weights : ∀ e∈entries,(Code.ofRat e.1).bits ≤ 2*n*n*L+4 := by
    intro e member
    have bound := (verified.weight_words e member).2.2
    rw [←matrixEq] at bound
    change (Code.ofRat e.1).bits ≤ 2*FlowDecomposition.denominatorInputBits matrix+4 at bound
    nlinarith
  have pbits : ∀ v : Fin n,(Code.ofRat (Vector.ofFn f.physical)[v.val]).bits+1 ≤ L := by
    simpa only [Vector.getElem_ofFn] using physicalBits
  have length := (WeightedLength.run_words (Vector.ofFn f.physical) entries L (2*n*n*L+4) constant pbits weights).mono
    (show _ ≤ K by
      apply le_trans (b:=WeightedLength.wordBudget n (n*n+1) L (2*n*n*L+4))
      · dsimp only [WeightedLength.wordBudget]
        gcongr
        exact verified.sparse
      · dsimp[K,commodityWords];omega)
  have output := WeightedLength.run_bits (Vector.ofFn f.physical) entries L (2*n*n*L+4) constant pbits weights
  have outputK : (Code.ofRat (WeightedLength.run (Vector.ofFn f.physical) entries).value).bits ≤ K := by
    apply output.trans
    apply le_trans (b:=WeightedLength.outputBudget n (n*n+1) L (2*n*n*L+4))
    · dsimp only [WeightedLength.outputBudget]
      gcongr
      exact verified.sparse
    · dsimp[K,commodityWords];omega
  have returned : (FlowExtract.decompose input matrix (f.source i) (f.target i)).value=some entries := by
    rw [FlowExtract.decompose_value]
    exact (congrArg (fun mat=>FlowDecomposition.decompose input.graph (Equiv.refl _) mat (f.source i) (f.target i)) matrixEq).trans verified.returned
  have ii : i.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have:=i.isLt;dsimp[K,commodityWords];omega)
  have ni : n.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[K,commodityWords];omega)
  have one : 1 ≤ K := by dsimp[K,commodityWords];omega
  unfold commodity
  rw [show (Vector.ofFn f.source)[i.val]=f.source i by simp,
    show (Vector.ofFn f.target)[i.val]=f.target i by simp]
  unfold commodityAt
  dsimp only
  rw [returned]
  simp only [wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
    or_false,forall_eq_or_imp,forall_eq,and_true]
  aesop

end BuyAtBulk.Computation.Runtime.CompactLift
