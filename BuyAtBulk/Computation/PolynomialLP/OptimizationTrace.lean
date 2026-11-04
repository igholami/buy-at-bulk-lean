import BuyAtBulk.Computation.PolynomialLP.CoordinateTrace
import BuyAtBulk.Computation.PolynomialLP.VectorTrace
import BuyAtBulk.Computation.PolynomialLP.OutputEncoding

/-! The complete stored rational optimizer, with explicit root encoding
arithmetic, all decision and face queries, and list-index materialization. -/
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP
open Computation Computation.Runtime Rational ObjectiveRuntime InputTrace
variable {n m : ℕ}

structure OptimizerRoot (n m : ℕ) where
  input : Stored (n:=n) (m:=m+(n+n))
  coordinateBits : ℕ

def optimizerRoot (input : Stored (n:=n) (m:=m)) : Traced (OptimizerRoot n m) :=
  let budget := inputBudgetTrace input
  let nTwo := InputTrace.addNat n 2
  let L := mulNat nTwo.value budget.value
  let square := mulNat n n
  let product := mulNat n L.value
  let sum := InputTrace.addNat square.value product.value
  let extra := InputTrace.addNat sum.value 1
  let twice := mulNat 2 extra.value
  let K := InputTrace.addNat twice.value 2
  let table := integerizeTrace input
  let boxed := boxedTrace table.value
  ⟨⟨boxed.value,K.value⟩,budget.events++nTwo.events++L.events++square.events++product.events++
    sum.events++extra.events++twice.events++K.events++table.events++boxed.events++[⟨.cons,[n.size,m.size,K.value.size]⟩]⟩

@[simp] theorem optimizerRoot_value (input : Stored (n:=n) (m:=m)) :
    (optimizerRoot input).value=⟨(integerize input).boxed,coordinateBits input⟩ := by
  simp only [optimizerRoot,inputBudgetTrace_value,InputTrace.addNat_value,mulNat_value,
    integerizeTrace_value,boxedTrace_value,coordinateBits,integerL,pow_two]

def optimizeTrace (input : Stored (n:=n) (m:=m)) : Traced (Option (Vector ℚ n)) :=
  let root := optimizerRoot input
  let decision := Trace.decideBoxed root.value.input
  if decision.value then
    let recovered := recoverActual root.value.input root.value.coordinateBits
    match recovered.value with
    | none => ⟨none,root.events++decision.events++[⟨.branch,[1]⟩]++recovered.events++[⟨.branch,[1]⟩]⟩
    | some value =>
      let face := fixTrace root.value.input root.value.input.objective value
      let indices := indexList n
      let coordinates := coordinateLoopTrace root.value.coordinateBits indices.value face.value
      match coordinates.value with
      | none => ⟨none,root.events++decision.events++[⟨.branch,[1]⟩]++recovered.events++[⟨.branch,[1]⟩]++
          face.events++indices.events++coordinates.events++[⟨.branch,[1]⟩]⟩
      | some values =>
        let vector := vectorFromListTrace values n
        ⟨vector.value,root.events++decision.events++[⟨.branch,[1]⟩]++recovered.events++[⟨.branch,[1]⟩]++
          face.events++indices.events++coordinates.events++[⟨.branch,[1]⟩]++vector.events⟩
  else ⟨none,root.events++decision.events++[⟨.branch,[1]⟩]⟩

@[simp] theorem optimizeTrace_value (input : Stored (n:=n) (m:=m)) :
    (optimizeTrace input).value=optimize input := by
  simp only [optimizeTrace,optimizerRoot_value,Trace.decideBoxed_value,recoverActual_value,
    fixTrace_value,indexList_value,coordinateLoopTrace_value,vectorFromListTrace_value,optimize]
  split <;> rename_i decision
  · split <;> simp_all only [Option.bind_none,Option.bind_some]
    split <;> simp_all only [Option.bind_none,Option.bind_some]
  · rfl

def rootCellBits (n B : ℕ) := (n+2)*B+2*B+10

theorem optimizerRoot_cells (input : Stored (n:=n) (m:=m)) :
    CellBits (integerize input).boxed (rootCellBits n (inputBudget input)) := by
  have integer := integerized_boxed_bits input
  constructor
  · intro i j
    exact (integer.1 i j).trans (by dsimp only [rootCellBits,integerL]; omega)
  · intro i
    exact (integer.2 i).trans (by dsimp only [rootCellBits,integerL]; omega)
  · intro j
    have source := (input_cellBits input).objective j
    change (Code.ofRat input.objective[j.val]).bits≤_
    exact source.trans (by dsimp only [rootCellBits]; omega)

/-- The initial attained objective has a source-derived encoding; later
coordinate faces use the smaller original coordinate encoding directly. -/
theorem recoveredValue_bits (input : Stored (n:=n) (m:=m)) (K : ℕ)
    (cube : input.problem.InUnitCube) (nonempty : ∃ x,input.problem.Feasible x)
    (vertex_words : ∀ x,input.problem.Feasible x → input.problem.Vertex x →
      ∀ j,(Code.ofRat (x j)).bits≤K)
    (value : ℚ) (computed : recoverValue input K=some value) :
    (Code.ofRat value).bits≤valueBits input K := by
  obtain ⟨q,returned,x,hx,hv,equality,_⟩ := recoverValue_correct input K cube nonempty vertex_words
  have same : q=value := Option.some.inj (returned.symm.trans computed)
  rw [←same,←equality]
  simpa only [valueBits,Fintype.card_fin] using linearForm_bits input.problem.objective x
    (objectiveBits input) K (objectiveBits_bound input) (vertex_words x hx hv)

end BuyAtBulk.PolynomialLP
