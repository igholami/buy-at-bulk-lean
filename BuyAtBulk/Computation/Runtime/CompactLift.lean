import BuyAtBulk.Computation.Runtime.CompactDecode
import BuyAtBulk.Computation.Runtime.WeightedLength
import BuyAtBulk.Computation.Runtime.FlowDecomposition
import BuyAtBulk.Computation.PolynomialLP.CompactOptimization
import BuyAtBulk.Computation.FlowDecomposition.Lift

/-! Actual optimizer-vector decomposition and weighted length metadata. Every
numerical input is stored; compact solutions occur only in the correctness proof. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.Computation.Runtime.CompactLift
open Rational BuyAtBulk.PolynomialLP.CompactEncoding
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

def commodityAt (physical : Vector ℚ n) (source target : Fin n)
    (point : Vector ℚ (variableCount n h)) (i : Fin h) : Traced (Option ℚ) :=
  let matrix : Traced (FlowDecomposition.FlowMatrix n) := CompactDecode.transportMatrix (n:=n) (h:=h) point i
  let decomposed : Traced (Option (FlowDecomposition.WeightedPaths input.graph source target)) :=
    FlowExtract.decompose input matrix.value source target
  let beforeEvents : List Event := matrix.events++[⟨.read,[i.val.size,n.size]⟩,⟨.read,[i.val.size,n.size]⟩]++decomposed.events
  match decomposed.value with
  | none => ⟨none,beforeEvents++([⟨.branch,[1]⟩,⟨.write,[1]⟩] : List Event)⟩
  | some entries =>
    let length := WeightedLength.run physical entries
    ⟨some length.value,beforeEvents++([⟨.branch,[1]⟩] : List Event)++length.events++([⟨.write,[1,(Code.ofRat length.value).bits]⟩] : List Event)⟩

def commodity (physical : Vector ℚ n) (source target : Vector (Fin n) h)
    (point : Vector ℚ (variableCount n h)) (i : Fin h) : Traced (Option ℚ) :=
  commodityAt input physical source[i.val] target[i.val] point i

theorem transportMatrix_eq (f : CompactFlow.Solution input.graph h)
    (point : Vector ℚ (variableCount n h))
    (coordinates : f.coordinates=decode (fun j=>point[j.val])) (i : Fin h) :
    (CompactDecode.transportMatrix point i).value=FlowDecomposition.storedMatrix input.graph (Equiv.refl _) f i := by
  apply Vector.ext
  intro u hu
  apply Vector.ext
  intro v hv
  have coord := congrFun coordinates (Sum.inr (Sum.inr (i,(⟨u,hu⟩ : Fin n),(⟨v,hv⟩ : Fin n))))
  change f.transport i ⟨u,hu⟩ ⟨v,hv⟩=point[(variableEquiv n h (Sum.inr (Sum.inr (i,⟨u,hu⟩,⟨v,hv⟩)))).val] at coord
  simpa only [FlowDecomposition.storedMatrix,Vector.getElem_ofFn,Equiv.refl_symm,Equiv.refl_apply] using
    (CompactDecode.transportMatrix_value point i ⟨u,hu⟩ ⟨v,hv⟩).trans coord.symm

theorem commodity_value (f : CompactFlow.Solution input.graph h) (point : Vector ℚ (variableCount n h))
    (coordinates : f.coordinates=decode (fun j=>point[j.val])) (i : Fin h) :
    (commodity input (Vector.ofFn f.physical) (Vector.ofFn f.source) (Vector.ofFn f.target) point i).value=
      some (FlowDecomposition.fractionalLength input.graph (Equiv.refl _) f i) := by
  have returned := (FlowDecomposition.entries_verified input.graph (Equiv.refl _) f i).returned
  have src : (Vector.ofFn f.source)[i.val]=f.source i := by simp
  have tgt : (Vector.ofFn f.target)[i.val]=f.target i := by simp
  unfold commodity
  rw [src,tgt]
  unfold commodityAt
  simp only [transportMatrix_eq input f point coordinates,FlowExtract.decompose_value,returned]
  simp only [WeightedLength.run_value,FlowDecomposition.fractionalLength,Vector.getElem_ofFn,Fin.eta]

def commodityCount (n : ℕ) := 11*n^2+3*n+(n*n+1)*FlowExtract.stepBudget n+(4*n+16)*(n*n+1)+20

theorem commodity_count (f : CompactFlow.Solution input.graph h) (point : Vector ℚ (variableCount n h))
    (coordinates : f.coordinates=decode (fun j=>point[j.val])) (i : Fin h) :
    (commodity input (Vector.ofFn f.physical) (Vector.ofFn f.source) (Vector.ofFn f.target) point i).events.length ≤ commodityCount n := by
  have matrix := CompactDecode.transportMatrix_count point i
  have search := FlowExtract.decompose_count input (CompactDecode.transportMatrix point i).value (f.source i) (f.target i)
  have returned := (FlowDecomposition.entries_verified input.graph (Equiv.refl _) f i).returned
  have sparse := (FlowDecomposition.entries_verified input.graph (Equiv.refl _) f i).sparse
  have length := WeightedLength.run_count (Vector.ofFn f.physical) (FlowDecomposition.entries input.graph (Equiv.refl _) f i)
  have matrixEq := transportMatrix_eq input f point coordinates i
  have src : (Vector.ofFn f.source)[i.val]=f.source i := by simp
  have tgt : (Vector.ofFn f.target)[i.val]=f.target i := by simp
  unfold commodity
  rw [src,tgt]
  unfold commodityAt
  simp only [matrixEq,FlowExtract.decompose_value,returned,List.length_append,List.length_cons,List.length_nil]
  rw [matrixEq] at search
  dsimp only [commodityCount]
  nlinarith

end BuyAtBulk.Computation.Runtime.CompactLift
