import BuyAtBulk.Computation.PolynomialLP.CompactConstraints
import BuyAtBulk.Computation.PolynomialLP.CompactCoefficients
import BuyAtBulk.Computation.Runtime.Weights

/-! Dense source compact LP materialization. Runtime dimensions are computed
once and carried with the arrays; casts preserve the stored payload and occur
only to relate the cached dimensions to the mathematical indexing formulas. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP.CompactTrace
open Computation Computation.Runtime Computation.Rational
variable {n h : ℕ}

structure Dimensions (n h : ℕ) where
  variableSize : ℕ
  constraints : ℕ
  variables_eq : variableSize=CompactEncoding.variableCount n h
  constraints_eq : constraints=CompactEncoding.constraintCount n h

def dimensions (n h : ℕ) : Traced (Dimensions n h) :=
  let nc := natMul h n
  let sq := natMul n n
  let tc := natMul h sq.value
  let both := addNat nc.value tc.value
  let vars := addNat n both.value
  let bc := natMul 4 nc.value
  let inner := addNat bc.value tc.value
  let right := addNat nc.value inner.value
  let box := natMul 2 vars.value
  let rows := addNat box.value right.value
  ⟨⟨vars.value,rows.value,rfl,rfl⟩,
    nc.events++sq.events++tc.events++both.events++vars.events++bc.events++inner.events++right.events++
      box.events++rows.events++[⟨.write,[vars.value.size,rows.value.size]⟩]⟩

@[simp] theorem dimensions_variables (n h : ℕ) : (dimensions n h).value.variableSize=CompactEncoding.variableCount n h := rfl
@[simp] theorem dimensions_constraints (n h : ℕ) : (dimensions n h).value.constraints=CompactEncoding.constraintCount n h := rfl
@[simp] theorem dimensions_count (n h : ℕ) : (dimensions n h).events.length=11 := by
  simp [dimensions,natMul,addNat,List.length_append]

def cell (data : CompactEncoding.Data n h) (dims : Dimensions n h)
    (row : CompactFlow.ConstraintIndex (Fin n) h) (j : Fin dims.variableSize) : Traced ℚ := do
  let c ← variableIndex n h (j.cast dims.variables_eq)
  literalCoefficient data row c

def matrixRow (data : CompactEncoding.Data n h) (dims : Dimensions n h) (i : Fin dims.constraints) :
    Traced (Vector ℚ dims.variableSize) := do
  let r ← constraintIndex n h (i.cast dims.constraints_eq)
  Weights.materialize (cell data dims r) (fun q => (Code.ofRat q).bits)

def boundCell (data : CompactEncoding.Data n h) (dims : Dimensions n h) (i : Fin dims.constraints) : Traced ℚ := do
  let r ← constraintIndex n h (i.cast dims.constraints_eq)
  literalBound data r

def objectiveCell (data : CompactEncoding.Data n h) (dims : Dimensions n h) (j : Fin dims.variableSize) : Traced ℚ := do
  let c ← variableIndex n h (j.cast dims.variables_eq)
  literalObjective data c

def storedAt (data : CompactEncoding.Data n h) (dims : Dimensions n h) :
    Traced (Stored (n:=dims.variableSize) (m:=dims.constraints)) := do
  let coefficients ← Weights.materialize (matrixRow data dims) (fun _ => dims.variableSize.size)
  let bounds ← Weights.materialize (boundCell data dims) (fun q => (Code.ofRat q).bits)
  let objective ← Weights.materialize (objectiveCell data dims) (fun q => (Code.ofRat q).bits)
  emit .write [dims.variableSize.size,dims.constraints.size] ⟨coefficients,bounds,objective⟩

def castStored {a b : ℕ} (input : Stored (n:=a) (m:=b)) (varEq : a=CompactEncoding.variableCount n h)
    (rowEq : b=CompactEncoding.constraintCount n h) :
    Stored (n:=CompactEncoding.variableCount n h) (m:=CompactEncoding.constraintCount n h) :=
  varEq ▸ rowEq ▸ input

structure Prepared (n h : ℕ) where
  dims : Dimensions n h
  input : Stored (n:=dims.variableSize) (m:=dims.constraints)

def Prepared.logical (prepared : Prepared n h) :
    Stored (n:=CompactEncoding.variableCount n h) (m:=CompactEncoding.constraintCount n h) :=
  castStored prepared.input prepared.dims.variables_eq prepared.dims.constraints_eq

def prepare (data : CompactEncoding.Data n h) : Traced (Prepared n h) :=
  let dims := dimensions n h
  let input := storedAt data dims.value
  ⟨⟨dims.value,input.value⟩,dims.events++input.events++[⟨.write,[dims.value.variableSize.size,dims.value.constraints.size]⟩]⟩

theorem storedAt_value (data : CompactEncoding.Data n h) (dims : Dimensions n h) :
    castStored (storedAt data dims).value dims.variables_eq dims.constraints_eq=CompactEncoding.stored data := by
  rcases dims with ⟨nv,nc,vars,rows⟩
  subst nv
  subst nc
  change (storedAt data ⟨_,_,rfl,rfl⟩).value=CompactEncoding.stored data
  simp only [storedAt,Traced.bind_value,emit_value]
  congr 1
  · apply Vector.ext
    intro i hi
    apply Vector.ext
    intro j hj
    simp [Weights.materialize,matrixRow,cell,Traced.bind_value,constraint_value,variable_value,
      literalCoefficient_value,CompactEncoding.stored]
  · apply Vector.ext
    intro i hi
    simp [Weights.materialize,boundCell,Traced.bind_value,constraint_value,literalBound_value,CompactEncoding.stored]
  · apply Vector.ext
    intro j hj
    simp [Weights.materialize,objectiveCell,Traced.bind_value,variable_value,literalObjective_value,CompactEncoding.stored]

theorem prepare_value (data : CompactEncoding.Data n h) : (prepare data).value.logical=CompactEncoding.stored data :=
  storedAt_value data (dimensions n h).value


 theorem cell_count (data : CompactEncoding.Data n h) (dims : Dimensions n h)
    (row : CompactFlow.ConstraintIndex (Fin n) h) (j : Fin dims.variableSize) :
    (cell data dims row j).events.length≤88 := by
  have index := variable_count n h (j.cast dims.variables_eq)
  have scalar := literalCoefficient_count data row (variableIndex n h (j.cast dims.variables_eq)).value
  simp only [cell,Traced.bind_events,Traced.bind_value,List.length_append]
  omega

theorem matrixRow_count (data : CompactEncoding.Data n h) (dims : Dimensions n h) (i : Fin dims.constraints) :
    (matrixRow data dims i).events.length≤90*dims.variableSize+65 := by
  have index := constraint_count n h (i.cast dims.constraints_eq)
  have entries := Weights.materialize_count
    (cell data dims (constraintIndex n h (i.cast dims.constraints_eq)).value)
    (fun q => (Code.ofRat q).bits) 88 (cell_count data dims _)
  simp only [matrixRow,Traced.bind_events,Traced.bind_value,List.length_append]
  omega

theorem boundCell_count (data : CompactEncoding.Data n h) (dims : Dimensions n h) (i : Fin dims.constraints) :
    (boundCell data dims i).events.length≤96 := by
  have index := constraint_count n h (i.cast dims.constraints_eq)
  have scalar := literalBound_count data (constraintIndex n h (i.cast dims.constraints_eq)).value
  simp only [boundCell,Traced.bind_events,Traced.bind_value,List.length_append]
  omega

theorem objectiveCell_count (data : CompactEncoding.Data n h) (dims : Dimensions n h) (j : Fin dims.variableSize) :
    (objectiveCell data dims j).events.length≤32 := by
  have index := variable_count n h (j.cast dims.variables_eq)
  have scalar := literalObjective_count data (variableIndex n h (j.cast dims.variables_eq)).value
  simp only [objectiveCell,Traced.bind_events,Traced.bind_value,List.length_append]
  omega

def frontendCount (n h : ℕ) :=
  256*(CompactEncoding.constraintCount n h+1)*(CompactEncoding.variableCount n h+1)+16

theorem storedAt_count (data : CompactEncoding.Data n h) (dims : Dimensions n h) :
    (storedAt data dims).events.length≤256*(dims.constraints+1)*(dims.variableSize+1)+4 := by
  have matrix := Weights.materialize_count (matrixRow data dims) (fun _ => dims.variableSize.size)
    (90*dims.variableSize+65) (matrixRow_count data dims)
  have bounds := Weights.materialize_count (boundCell data dims) (fun q => (Code.ofRat q).bits)
    96 (boundCell_count data dims)
  have objective := Weights.materialize_count (objectiveCell data dims) (fun q => (Code.ofRat q).bits)
    32 (objectiveCell_count data dims)
  simp only [storedAt,Traced.bind_events,Traced.bind_value,List.length_append,emit_length]
  nlinarith

theorem prepare_count (data : CompactEncoding.Data n h) :
    (prepare data).events.length≤frontendCount n h := by
  have entries := storedAt_count data (dimensions n h).value
  simp only [prepare,List.length_append,dimensions_count,List.length_cons,List.length_nil]
  simpa only [dimensions_variables,dimensions_constraints,frontendCount] using (show
    11+(storedAt data (dimensions n h).value).events.length+1≤
      256*((dimensions n h).value.constraints+1)*((dimensions n h).value.variableSize+1)+16 by omega)

def frontendWords (n h L : ℕ) := indexBudget n h+scalarWords n h L+
  CompactEncoding.variableCount n h+CompactEncoding.constraintCount n h+n+h+16

theorem dimensions_words (n h : ℕ) :
    WordsWithin (indexBudget n h) (dimensions n h).events := by
  simp only [dimensions,Traced.bind_events,Traced.bind_value,natMul,addNat,emit,
    wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
    or_false,forall_eq_or_imp,forall_eq,and_true]
  repeat' apply And.intro
  all_goals
    apply (Nat.size_le.mpr Nat.lt_two_pow_self).trans
    dsimp only [indexBudget,CompactEncoding.variableCount,CompactEncoding.constraintCount]
    omega

theorem cell_words (data : CompactEncoding.Data n h) (dims : Dimensions n h)
    (row : CompactFlow.ConstraintIndex (Fin n) h) (j : Fin dims.variableSize) (L : ℕ) :
    WordsWithin (frontendWords n h L) (cell data dims row j).events := by
  let W := frontendWords n h L
  have index := variable_words n h (j.cast dims.variables_eq) W
    (by dsimp only [W,frontendWords,indexBudget,CompactEncoding.variableCount]; omega)
  have scalar := (literalCoefficient_words data row (variableIndex n h (j.cast dims.variables_eq)).value L).mono
    (show _≤W by dsimp only [W,frontendWords]; omega)
  simpa only [cell,Traced.bind_events,Traced.bind_value,wordsWithin_append] using And.intro index scalar

theorem cell_bits (data : CompactEncoding.Data n h) (dims : Dimensions n h)
    (row : CompactFlow.ConstraintIndex (Fin n) h) (j : Fin dims.variableSize) :
    (Code.ofRat (cell data dims row j).value).bits≤4 := by
  simpa only [cell,Traced.bind_value] using literalCoefficient_bits data row (variableIndex n h (j.cast dims.variables_eq)).value

theorem matrixRow_words (data : CompactEncoding.Data n h) (dims : Dimensions n h)
    (i : Fin dims.constraints) (L : ℕ) : WordsWithin (frontendWords n h L) (matrixRow data dims i).events := by
  let W := frontendWords n h L
  have index := constraint_words n h (i.cast dims.constraints_eq) W
    (by dsimp only [W,frontendWords]; omega)
  have entries := Weights.materialize_words
    (cell data dims (constraintIndex n h (i.cast dims.constraints_eq)).value)
    (fun q => (Code.ofRat q).bits) W
    (by rw [dims.variables_eq]; dsimp only [W,frontendWords]; omega)
    (fun j => cell_words data dims _ j L)
    (fun j => (cell_bits data dims _ j).trans (by dsimp only [W,frontendWords,scalarWords]; omega))
  simpa only [matrixRow,Traced.bind_events,Traced.bind_value,wordsWithin_append] using And.intro index entries

theorem boundCell_words (data : CompactEncoding.Data n h) (dims : Dimensions n h)
    (i : Fin dims.constraints) (L : ℕ) : WordsWithin (frontendWords n h L) (boundCell data dims i).events := by
  let W := frontendWords n h L
  have index := constraint_words n h (i.cast dims.constraints_eq) W
    (by dsimp only [W,frontendWords]; omega)
  have scalar := (literalBound_words data (constraintIndex n h (i.cast dims.constraints_eq)).value L).mono
    (show _≤W by dsimp only [W,frontendWords]; omega)
  simpa only [boundCell,Traced.bind_events,Traced.bind_value,wordsWithin_append] using And.intro index scalar

theorem objectiveCell_words (data : CompactEncoding.Data n h) (dims : Dimensions n h)
    (j : Fin dims.variableSize) (L : ℕ)
    (buying : ∀ v : Fin n,(Code.ofRat data.buying[v.val]).bits≤L)
    (physical : ∀ v : Fin n,(Code.ofRat data.physical[v.val]).bits≤L)
    (demand : ∀ i : Fin h,(Code.ofRat data.demand[i.val]).bits≤L) :
    WordsWithin (frontendWords n h L) (objectiveCell data dims j).events := by
  let W := frontendWords n h L
  have index := variable_words n h (j.cast dims.variables_eq) W
    (by dsimp only [W,frontendWords,indexBudget,CompactEncoding.variableCount]; omega)
  have scalar := (literalObjective_words data (variableIndex n h (j.cast dims.variables_eq)).value L buying physical demand).mono
    (show _≤W by dsimp only [W,frontendWords]; omega)
  simpa only [objectiveCell,Traced.bind_events,Traced.bind_value,wordsWithin_append] using And.intro index scalar

theorem storedAt_words (data : CompactEncoding.Data n h) (dims : Dimensions n h) (L : ℕ)
    (buying : ∀ v : Fin n,(Code.ofRat data.buying[v.val]).bits≤L)
    (physical : ∀ v : Fin n,(Code.ofRat data.physical[v.val]).bits≤L)
    (demand : ∀ i : Fin h,(Code.ofRat data.demand[i.val]).bits≤L) :
    WordsWithin (frontendWords n h L) (storedAt data dims).events := by
  let W := frontendWords n h L
  have rows : dims.constraints≤W := by rw [dims.constraints_eq]; dsimp only [W,frontendWords]; omega
  have cols : dims.variableSize≤W := by rw [dims.variables_eq]; dsimp only [W,frontendWords]; omega
  have rowWidth : dims.variableSize.size≤W := (Nat.size_le.mpr Nat.lt_two_pow_self).trans cols
  have rowCount : dims.constraints.size≤W := (Nat.size_le.mpr Nat.lt_two_pow_self).trans rows
  have matrix := Weights.materialize_words (matrixRow data dims) (fun _ => dims.variableSize.size) W rows
    (fun i => matrixRow_words data dims i L) (fun _ => rowWidth)
  have bounds := Weights.materialize_words (boundCell data dims) (fun q => (Code.ofRat q).bits) W rows
    (fun i => boundCell_words data dims i L)
    (fun i => (literalBound_bits data (constraintIndex n h (i.cast dims.constraints_eq)).value).trans
      (show 4≤W by dsimp only [W,frontendWords,scalarWords]; omega))
  have objective := Weights.materialize_words (objectiveCell data dims) (fun q => (Code.ofRat q).bits) W cols
    (fun j => objectiveCell_words data dims j L buying physical demand)
    (fun j => (literalObjective_bits data (variableIndex n h (j.cast dims.variables_eq)).value L buying physical demand).trans
      (show 4*L+8≤W by dsimp only [W,frontendWords,scalarWords]; omega))
  simpa only [storedAt,Traced.bind_events,Traced.bind_value,emit,wordsWithin_append,
    wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,
    forall_eq_or_imp,forall_eq,and_true] using And.intro matrix (And.intro bounds (And.intro objective (And.intro rowWidth rowCount)))

theorem prepare_words (data : CompactEncoding.Data n h) (L : ℕ)
    (buying : ∀ v : Fin n,(Code.ofRat data.buying[v.val]).bits≤L)
    (physical : ∀ v : Fin n,(Code.ofRat data.physical[v.val]).bits≤L)
    (demand : ∀ i : Fin h,(Code.ofRat data.demand[i.val]).bits≤L) :
    WordsWithin (frontendWords n h L) (prepare data).events := by
  have header := (dimensions_words n h).mono
    (show _≤frontendWords n h L by dsimp only [frontendWords]; omega)
  have entries := storedAt_words data (dimensions n h).value L buying physical demand
  have cols : (dimensions n h).value.variableSize.size≤frontendWords n h L :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by rw [dimensions_variables]; dsimp only [frontendWords]; omega)
  have rows : (dimensions n h).value.constraints.size≤frontendWords n h L :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by rw [dimensions_constraints]; dsimp only [frontendWords]; omega)
  simpa only [prepare,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,
    List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true] using
    And.intro (And.intro header entries) (And.intro cols rows)

end BuyAtBulk.PolynomialLP.CompactTrace
