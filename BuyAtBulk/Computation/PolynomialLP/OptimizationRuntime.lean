import BuyAtBulk.Computation.PolynomialLP.OptimizerRootRuntime

/-! Closed polynomial event and word bounds for the unconditional native exact
optimizer. All successful face encodings come from vertices of the original
boxed system. No running-time, separation, or optimization certificate is input. -/
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP
open Computation Computation.Runtime Rational ObjectiveRuntime InputTrace
variable {n m : ℕ}

def optimizerK (n B : ℕ) := 2*(n^2+n*((n+2)*B)+1)+2
def optimizerL (n B : ℕ) := rootCellBits n B

def optimizerFaceL (n B : ℕ) := optimizerL n B+optimizerK n B+
  valueBudget n (n*optimizerL n B) (optimizerK n B)+4

def optimizerRows (n m : ℕ) := m+(n+n)+2+2*n

def optimizerRootSize (n m B : ℕ) :=
  1+((m+(n+n))+(m+(n+n))*n+n)*optimizerL n B

def optimizerCount (n m B : ℕ) :=
  optimizerRootCount n m B+Trace.decisionCount n (m+(n+n)) (optimizerRootSize n m B)+
    recoverCount n (m+(n+n)) (optimizerL n B) (optimizerK n B)+
    (2*(m+(n+n))+1)*(3*n+13)+4*n+12+3*n+
    coordinateLoopCount n (optimizerRows n m) (optimizerFaceL n B) (optimizerK n B) n+
    vectorFromListCount n+3

def optimizerWords (n m B : ℕ) :=
  optimizerRootWords n m B+Trace.decisionWordBudget n (m+(n+n)) (optimizerRootSize n m B)+
    recoverWordBudget n (m+(n+n)) (optimizerL n B) (optimizerK n B)+
    coordinateLoopWords n (optimizerRows n m) (optimizerFaceL n B) (optimizerK n B)+
    optimizerFaceL n B+optimizerRows n m+optimizerK n B+n+20

theorem optimizeTrace_runtime (input : Stored (n:=n) (m:=m)) :
    (optimizeTrace input).value=optimize input ∧
      (optimizeTrace input).events.length≤optimizerCount n m (inputBudget input) ∧
      WordsWithin (optimizerWords n m (inputBudget input)) (optimizeTrace input).events := by
  refine ⟨optimizeTrace_value input,?_⟩
  let B := inputBudget input
  let root := (integerize input).boxed
  let K := optimizerK n B
  let L := optimizerL n B
  let H := optimizerFaceL n B
  let M := optimizerRows n m
  let W := optimizerWords n m B
  have root_cells : CellBits root L := optimizerRoot_cells input
  have root_size : inputBudget root≤optimizerRootSize n m B := root_cells.inputBudget
  have rootCount := optimizerRoot_count input
  have decisionCount := (Trace.decideBoxed_count root).trans
    (Trace.decisionCount_mono (le_refl n) (le_refl _) root_size)
  have rootWords : WordsWithin W (optimizerRoot input).events := (optimizerRoot_words input).mono
    (by dsimp only [W,optimizerWords,B]; omega)
  have decisionWords : WordsWithin W (Trace.decideBoxed root).events :=
    (Trace.decideBoxed_words root).mono
      ((Trace.decisionWordBudget_mono (le_refl n) (le_refl _) root_size).trans
        (by dsimp only [W,optimizerWords]; omega))
  have small : n+M+H+K+4≤W := by dsimp only [W,optimizerWords,M,H,K]; omega
  have HL : L≤H := by dsimp only [L,H,optimizerFaceL]; omega
  have HK : K≤H := by dsimp only [K,H,optimizerFaceL]; omega
  have Hfour : 4≤H := by dsimp only [H,optimizerFaceL]; omega
  have Keq : coordinateBits input=K := rfl
  change (optimizeTrace input).events.length≤optimizerCount n m (inputBudget input) ∧ WordsWithin W (optimizeTrace input).events
  by_cases yes : decideBoxed root=true
  · have cube : root.problem.InUnitCube := (integerize input).boxed_in_cube
    have nonempty : ∃ x,root.problem.Feasible x := (decide_correct_in_cube root cube).mp yes
    have vertex_words : ∀ x,root.problem.Feasible x → root.problem.Vertex x →
        ∀ j,(Code.ofRat (x j)).bits≤K := fun x _ hv => root_vertex_words input x hv
    obtain ⟨value,computed,v,vfeasible,vvertex,value_eq,minimal⟩ :=
      recoverValue_correct root K cube nonempty vertex_words
    have scalar := recoveredValue_bits root K cube nonempty vertex_words value computed
    have valueBudgetBound := valueBudget_mono (le_refl n) (objectiveBits_le root_cells) (le_refl K)
    change valueBits root K≤valueBudget n (n*L) K at valueBudgetBound
    have scalarH : (Code.ofRat value).bits≤H := scalar.trans (valueBudgetBound.trans
      (by dsimp only [H,optimizerFaceL,L,K]; omega))
    let face := root.fix root.objective value
    have face_subset : ∀ x,face.problem.Feasible x → root.problem.Feasible x :=
      fun x hx => ((root.fix_feasible root.objective value x).mp hx).1
    have face_vertices : ∀ x,face.problem.Feasible x → face.problem.Vertex x → root.problem.Vertex x := by
      intro x hx hv
      have equality := ((root.fix_feasible root.objective value x).mp hx).2
      apply root.fix_vertex value x hx _ hv
      intro y hy
      change rowForm root.objective x≤_
      rw [equality]
      exact minimal y hy
    have face_nonempty : ∃ x,face.problem.Feasible x :=
      ⟨v,(root.fix_feasible root.objective value v).mpr ⟨vfeasible,value_eq⟩⟩
    have face_cells : CellBits face H :=
      (root_cells.mono HL).fix _ _ (fun j => (root_cells.objective j).trans HL) scalarH
    obtain ⟨values,returned,x,hx,related,xvertex⟩ := coordinateLoop_correct root K cube vertex_words
      (List.finRange n) face face_subset face_vertices face_nonempty
    have length : values.length=n := by simpa using related.length_eq.symm
    have valuesWords : ∀ q∈values,(Code.ofRat q).bits≤K := by
      intro q member
      obtain ⟨j,hj,equality⟩ := List.mem_iff_getElem.mp member
      have bound : j<n := by omega
      have rel := related.get (by simpa using bound) hj
      have indexeq : (List.finRange n).get ⟨j,by simpa using bound⟩ = ⟨j,bound⟩ := by
        apply Fin.ext
        simp
      have coordinate : x ⟨j,bound⟩=q := by simpa only [indexeq] using rel.trans equality
      rw [←coordinate]
      exact vertex_words x (face_subset x hx) xvertex ⟨j,bound⟩
    have coords := coordinateLoopTrace_runtime root K H M cube vertex_words Hfour HK
      (List.finRange n) face (by simp only [List.length_finRange]; dsimp only [M,optimizerRows]; omega)
      face_cells face_subset face_vertices face_nonempty
    have recoverCount := recoverActual_count root L K root_cells
    have fixedCount := fixTrace_count root root.objective value
    have vectorCount := vectorFromListTrace_count values n length
    have recoverWords : WordsWithin W (recoverActual root K).events :=
      (recoverActual_words root L K root_cells).mono (by dsimp only [W,optimizerWords,L,K]; omega)
    have fixedWords := fixTrace_words root root.objective value W
      (by dsimp only [M,optimizerRows] at small; omega)
      (fun i j => (root_cells.coefficients i j).trans (HL.trans (by omega)))
      (fun i => (root_cells.bounds i).trans (HL.trans (by omega)))
      (fun j => (root_cells.objective j).trans (HL.trans (by omega))) (scalarH.trans (by omega))
    have coordsWords := coords.2.mono (show coordinateLoopWords n M H K≤W by dsimp only [W,optimizerWords,M,H,K]; omega)
    have indicesWords := indexList_words n W (by omega)
    have vectorWords := vectorFromListTrace_words values n W length (by omega)
      (fun q member => (valuesWords q member).trans (by omega))
    have computedTrace : (recoverActual root K).value=some value := (recoverActual_value root K).trans computed
    have returnedTrace : (coordinateLoopTrace K (List.finRange n) face).value=some values :=
      (coordinateLoopTrace_value K _ face).trans returned
    simp only [optimizeTrace,optimizerRoot_value,Trace.decideBoxed_value]
    simp only [← show root=(integerize input).boxed from rfl]
    rw [Keq,if_pos yes,computedTrace]
    simp only [fixTrace_value,indexList_value]
    simp only [← show face=root.fix root.objective value from rfl]
    rw [returnedTrace]
    constructor
    · simp only [List.length_append,List.length_cons,List.length_nil,indexList_count]
      have cc := coords.1
      simp only [List.length_finRange] at cc
      dsimp only [optimizerCount]
      dsimp only [B,root,K,L,M,H,optimizerK,optimizerL,optimizerRows,optimizerFaceL] at *
      omega
    · simp only [wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,
        List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨rootWords,decisionWords⟩,by omega⟩,recoverWords⟩,by omega⟩,fixedWords⟩,indicesWords⟩,coordsWords⟩,by omega⟩,vectorWords⟩
  · simp only [optimizeTrace,optimizerRoot_value,Trace.decideBoxed_value]
    simp only [← show root=(integerize input).boxed from rfl]
    rw [if_neg yes]
    constructor
    · simp only [List.length_append,List.length_cons,List.length_nil]
      dsimp only [optimizerCount,B,root] at decisionCount ⊢
      omega
    · simp only [wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,
        List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
      exact ⟨⟨rootWords,decisionWords⟩,by omega⟩
end BuyAtBulk.PolynomialLP
