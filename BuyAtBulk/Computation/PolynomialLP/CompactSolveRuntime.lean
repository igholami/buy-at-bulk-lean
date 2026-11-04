import BuyAtBulk.Computation.PolynomialLP.CompactTrace
import BuyAtBulk.Computation.PolynomialLP.OptimizerMonotonicity

/-! Literal compact source arrays are materialized, optimized by the actual
unconditional program, and returned with their computed dimension cast erased.
The bounds depend only on source dimensions and source scalar word lengths. -/
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP.CompactEncoding
open Computation Computation.Runtime Rational
variable {n h : ℕ}

def solveTrace (data : Data n h) : Traced (Option (Vector ℚ (variableCount n h))) :=
  let prepared := CompactTrace.prepare data
  let solved := optimizeTrace prepared.value.input
  ⟨solved.value.map (fun point => point.cast prepared.value.dims.variables_eq),
    prepared.events++solved.events++[⟨.branch,[1]⟩,⟨.write,[prepared.value.dims.variableSize.size]⟩]⟩

theorem optimize_castStored {a b : ℕ} (input : Stored (n:=a) (m:=b))
    (vars : a=variableCount n h) (rows : b=constraintCount n h) :
    (optimize input).map (fun point => point.cast vars)=optimize (CompactTrace.castStored input vars rows) := by
  subst a
  subst b
  simp only [CompactTrace.castStored,Vector.cast_rfl]
  change (optimize input).map id=optimize input
  simp

theorem inputBudget_castStored {a b : ℕ} (input : Stored (n:=a) (m:=b))
    (vars : a=variableCount n h) (rows : b=constraintCount n h) :
    inputBudget (CompactTrace.castStored input vars rows)=inputBudget input := by
  subst a
  subst b
  rfl

@[simp] theorem solveTrace_value (data : Data n h) : (solveTrace data).value=solve data := by
  simp only [solveTrace,optimizeTrace_value]
  exact (optimize_castStored (CompactTrace.prepare data).value.input
    (CompactTrace.prepare data).value.dims.variables_eq
    (CompactTrace.prepare data).value.dims.constraints_eq).trans
      (congrArg optimize (CompactTrace.prepare_value data))

 theorem prepared_inputBudget (data : Data n h) :
    inputBudget (CompactTrace.prepare data).value.input=inputBudget (stored data) := by
  rw [←CompactTrace.prepare_value data]
  exact (inputBudget_castStored _ _ _).symm

def denseCellBits (L : ℕ) := 4*L+8

theorem stored_cells (data : Data n h) (L : ℕ)
    (buying : ∀ v : Fin n,(Code.ofRat data.buying[v.val]).bits≤L)
    (physical : ∀ v : Fin n,(Code.ofRat data.physical[v.val]).bits≤L)
    (demand : ∀ i : Fin h,(Code.ofRat data.demand[i.val]).bits≤L) :
    CellBits (stored data) (denseCellBits L) := by
  constructor
  · intro i j
    simpa only [stored,Vector.getElem_ofFn] using (coefficient_bits data _ _).trans
      (show 4≤denseCellBits L by dsimp only [denseCellBits]; omega)
  · intro i
    simpa only [stored,Vector.getElem_ofFn] using (bound_bits data _).trans
      (show 4≤denseCellBits L by dsimp only [denseCellBits]; omega)
  · intro j
    have literal := CompactTrace.literalObjective_bits data ((variableEquiv n h).symm j) L buying physical demand
    simpa only [CompactTrace.literalObjective_value,stored,Vector.getElem_ofFn,denseCellBits] using literal

def denseInputBudget (n h L : ℕ) :=
  1+(constraintCount n h+constraintCount n h*variableCount n h+variableCount n h)*denseCellBits L

def solveCount (n h L : ℕ) := CompactTrace.frontendCount n h+
  optimizerCount (variableCount n h) (constraintCount n h) (denseInputBudget n h L)+2

def solveWords (n h L : ℕ) := CompactTrace.frontendWords n h L+
  optimizerWords (variableCount n h) (constraintCount n h) (denseInputBudget n h L)+variableCount n h+4

def solutionBits (n h L : ℕ) := optimizerK (variableCount n h) (denseInputBudget n h L)

theorem solveTrace_runtime (data : Data n h) (L : ℕ)
    (buying : ∀ v : Fin n,(Code.ofRat data.buying[v.val]).bits≤L)
    (physical : ∀ v : Fin n,(Code.ofRat data.physical[v.val]).bits≤L)
    (demand : ∀ i : Fin h,(Code.ofRat data.demand[i.val]).bits≤L) :
    (solveTrace data).value=solve data ∧
      (solveTrace data).events.length≤solveCount n h L ∧
      WordsWithin (solveWords n h L) (solveTrace data).events := by
  refine ⟨solveTrace_value data,?_⟩
  let prepared := (CompactTrace.prepare data).value
  have size : inputBudget prepared.input≤denseInputBudget n h L := by
    rw [prepared_inputBudget]
    exact (stored_cells data L buying physical demand).inputBudget
  have optimizer := optimizeTrace_runtime prepared.input
  have counted := optimizer.2.1
  have words := optimizer.2.2
  have countCapacity : optimizerCount prepared.dims.variableSize prepared.dims.constraints
      (inputBudget prepared.input)≤optimizerCount (variableCount n h) (constraintCount n h) (denseInputBudget n h L) := by
    exact optimizerCount_mono (Nat.le_of_eq prepared.dims.variables_eq) (Nat.le_of_eq prepared.dims.constraints_eq) size
  have countBound := counted.trans countCapacity
  have frontCount := CompactTrace.prepare_count data
  have frontWords := (CompactTrace.prepare_words data L buying physical demand).mono
    (show _≤solveWords n h L by dsimp only [solveWords]; omega)
  have optimizerWords : WordsWithin (solveWords n h L) (optimizeTrace prepared.input).events :=
    words.mono (by
      exact (optimizerWords_mono (Nat.le_of_eq prepared.dims.variables_eq) (Nat.le_of_eq prepared.dims.constraints_eq) size).trans
        (by dsimp only [solveWords]; omega))
  have columns : prepared.dims.variableSize.size≤solveWords n h L :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans
      (by rw [prepared.dims.variables_eq]; dsimp only [solveWords]; omega)
  constructor
  · simp only [solveTrace,List.length_append,List.length_cons,List.length_nil]
    dsimp only [solveCount]
    dsimp only [prepared] at countBound
    omega
  · simpa only [solveTrace,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
      List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true] using
      And.intro (And.intro frontWords optimizerWords) (And.intro (by dsimp only [solveWords]; omega : 1≤solveWords n h L) columns)

theorem solve_output_bits (data : Data n h) (L : ℕ)
    (buying : ∀ v : Fin n,(Code.ofRat data.buying[v.val]).bits≤L)
    (physical : ∀ v : Fin n,(Code.ofRat data.physical[v.val]).bits≤L)
    (demand : ∀ i : Fin h,(Code.ofRat data.demand[i.val]).bits≤L)
    (point : Vector ℚ (variableCount n h)) (actual : solve data=some point) :
    ∀ j : Fin (variableCount n h),(Code.ofRat point[j.val]).bits≤solutionBits n h L := by
  have bits := optimize_bits (stored data) point actual
  have size := (stored_cells data L buying physical demand).inputBudget
  intro j
  apply (bits j).trans
  change optimizerK (variableCount n h) (inputBudget (stored data))≤_
  dsimp only [solutionBits,optimizerK]
  gcongr
  exact size
end BuyAtBulk.PolynomialLP.CompactEncoding
