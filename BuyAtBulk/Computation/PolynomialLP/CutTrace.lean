import BuyAtBulk.Computation.PolynomialLP.CutData
import BuyAtBulk.Computation.Runtime.Weights

namespace BuyAtBulk.PolynomialLP
open Computation Computation.Runtime Computation.Rational
variable {n m : ℕ}

def copyRatVector (values : Vector ℚ n) : Traced (Vector ℚ n) :=
  Weights.materialize (readRat values) (fun q => (Code.ofRat q).bits)

@[simp] theorem copyRatVector_value (values : Vector ℚ n) : (copyRatVector values).value=values := by
  apply Vector.ext
  intro i hi
  simp [copyRatVector,Weights.materialize,readRat,emit]

theorem copyRatVector_count (values : Vector ℚ n) :
    (copyRatVector values).events.length≤3*n+1 := by
  simpa [copyRatVector,readRat,Nat.mul_comm] using Weights.materialize_count (readRat values)
    (fun q => (Code.ofRat q).bits) 1 (fun _ => by simp [readRat])

theorem copyRatVector_words (values : Vector ℚ n) (K : ℕ) (indices : n≤K)
    (cells : ∀ j : Fin n, (Code.ofRat values[j.val]).bits≤K) :
    WordsWithin K (copyRatVector values).events := by
  apply Weights.materialize_words _ _ _ indices
  · intro j
    have index : j.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
    simpa [readRat,emit,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp] using And.intro index (cells j)
  · simpa [readRat,emit] using cells

def copyMatrix (values : Vector (Vector ℚ n) m) : Traced (Vector (Vector ℚ n) m) :=
  Weights.materialize (fun i => do
    let row ← emit .read [i.val.size,n.size] values[i.val]
    copyRatVector row) (fun _ => n.size)

@[simp] theorem copyMatrix_value (values : Vector (Vector ℚ n) m) : (copyMatrix values).value=values := by
  apply Vector.ext
  intro i hi
  simp [copyMatrix,Weights.materialize,Traced.bind_value]

theorem copyMatrix_count (values : Vector (Vector ℚ n) m) :
    (copyMatrix values).events.length≤m*(3*n+4)+1 := by
  apply Weights.materialize_count
  intro i
  have bound := copyRatVector_count values[i.val]
  simp only [Traced.bind_events,Traced.bind_value,emit_value,emit_length,List.length_append]
  omega

theorem copyMatrix_words (values : Vector (Vector ℚ n) m) (K : ℕ)
    (columns : n≤K) (rows : m≤K)
    (cells : ∀ i : Fin m, ∀ j : Fin n, (Code.ofRat values[i.val][j.val]).bits≤K) :
    WordsWithin K (copyMatrix values).events := by
  apply Weights.materialize_words _ _ _ rows
  · intro i
    have index : i.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
    have width : n.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans columns
    have copied := copyRatVector_words values[i.val] K columns (cells i)
    simpa [Traced.bind_events,Traced.bind_value,emit,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
      List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp] using And.intro (And.intro index width) copied
  · intro i
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans columns

/-- Worst-case scalar/header copies when pushing into the two freshly copied
arrays. Exact-capacity allocation is not treated as spare capacity. -/
def pushCopies (input : Stored (n:=n) (m:=m)) : Traced Unit :=
  ⟨(),(List.finRange m).flatMap fun i =>
    [⟨.scan,[i.val.size]⟩,⟨.read,[i.val.size,n.size]⟩,⟨.write,[i.val.size,n.size]⟩,
     ⟨.scan,[i.val.size]⟩,⟨.read,[i.val.size,(Code.ofRat input.bounds[i.val]).bits]⟩,
     ⟨.write,[i.val.size,(Code.ofRat input.bounds[i.val]).bits]⟩]⟩

@[simp] theorem pushCopies_value (input : Stored (n:=n) (m:=m)) : (pushCopies input).value=() := rfl
@[simp] theorem pushCopies_count (input : Stored (n:=n) (m:=m)) :
    (pushCopies input).events.length=6*m := by
  simp [pushCopies,List.length_flatMap,Nat.mul_comm]

theorem pushCopies_words (input : Stored (n:=n) (m:=m)) (K : ℕ) (indices : n+m+2≤K)
    (bounds : ∀ i : Fin m, (Code.ofRat input.bounds[i.val]).bits≤K) :
    WordsWithin K (pushCopies input).events := by
  have dimension : n.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  intro event member word present
  obtain ⟨i,_,member⟩ := List.mem_flatMap.mp member
  have index : i.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := i.isLt;omega)
  have all : WordsWithin K
      [⟨Operation.scan,[i.val.size]⟩,⟨.read,[i.val.size,n.size]⟩,⟨.write,[i.val.size,n.size]⟩,
       ⟨.scan,[i.val.size]⟩,⟨.read,[i.val.size,(Code.ofRat input.bounds[i.val]).bits]⟩,
       ⟨.write,[i.val.size,(Code.ofRat input.bounds[i.val]).bits]⟩] := by
    simp only [wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,
      forall_eq_or_imp,forall_eq,and_true]
    aesop
  exact all event member word present

def addCutTrace (input : Stored (n:=n) (m:=m)) (row : Vector ℚ n) (bound : ℚ) :
    Traced (Stored (n:=n) (m:=m+1)) := do
  let rows ← copyMatrix input.coefficients
  let bounds ← copyRatVector input.bounds
  let _ ← pushCopies input
  let coefficients ← emit .write [m.size,n.size] (rows.push row)
  let bounds ← emit .write [m.size,(Code.ofRat bound).bits] (bounds.push bound)
  emit .write [n.size,(m+1).size] ⟨coefficients,bounds,input.objective⟩

@[simp] theorem addCutTrace_value (input : Stored (n:=n) (m:=m)) (row : Vector ℚ n) (bound : ℚ) :
    (addCutTrace input row bound).value=input.addCut row bound := by
  simp [addCutTrace,Traced.bind_value,Stored.addCut]

theorem addCutTrace_count (input : Stored (n:=n) (m:=m)) (row : Vector ℚ n) (bound : ℚ) :
    (addCutTrace input row bound).events.length≤m*(3*n+13)+5 := by
  have matrix := copyMatrix_count input.coefficients
  have rhs := copyRatVector_count input.bounds
  simp only [addCutTrace,Traced.bind_events,Traced.bind_value,List.length_append,emit_length,emit_value,pushCopies_count,pushCopies_value]
  nlinarith

theorem addCutTrace_words (input : Stored (n:=n) (m:=m)) (row : Vector ℚ n) (bound : ℚ) (K : ℕ)
    (indices : n+m+2≤K)
    (coefficients : ∀ i : Fin m, ∀ j : Fin n, (Code.ofRat input.coefficients[i.val][j.val]).bits≤K)
    (bounds : ∀ i : Fin m, (Code.ofRat input.bounds[i.val]).bits≤K)
    (scalar : (Code.ofRat bound).bits≤K) :
    WordsWithin K (addCutTrace input row bound).events := by
  have matrix := copyMatrix_words input.coefficients K (by omega) (by omega) coefficients
  have rhs := copyRatVector_words input.bounds K (by omega) bounds
  have pushed := pushCopies_words input K indices bounds
  have nsize : n.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have msize : m.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have nextsize : (m+1).size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  simpa only [addCutTrace,Traced.bind_events,Traced.bind_value,emit,wordsWithin_append,wordsWithin_cons,
    wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true] using
    And.intro matrix (And.intro rhs (And.intro pushed (And.intro (And.intro msize nsize)
      (And.intro (And.intro msize scalar) (And.intro nsize nextsize)))))

def negateRowTrace (row : Vector ℚ n) : Traced (Vector ℚ n) :=
  Weights.materialize (fun j => do
    let q ← readRat row j
    emit .ratNeg [(Code.ofRat q).bits,(Code.ofRat (-q)).bits] (-q))
    (fun q => (Code.ofRat q).bits)

@[simp] theorem negateRowTrace_value (row : Vector ℚ n) :
    (negateRowTrace row).value=row.map (-·) := by
  apply Vector.ext
  intro i hi
  simp [negateRowTrace,Weights.materialize,Traced.bind_value,readRat,emit]

theorem negateRowTrace_count (row : Vector ℚ n) : (negateRowTrace row).events.length≤4*n+1 := by
  simpa [negateRowTrace,Traced.bind_events,Traced.bind_value,readRat,Nat.mul_comm] using
    Weights.materialize_count (fun j => do
      let q ← readRat row j
      emit .ratNeg [(Code.ofRat q).bits,(Code.ofRat (-q)).bits] (-q))
      (fun q => (Code.ofRat q).bits) 2 (fun j => by simp [readRat,Traced.bind_events])

theorem negateRowTrace_words (row : Vector ℚ n) (K : ℕ) (indices : n≤K)
    (cells : ∀ j : Fin n, (Code.ofRat row[j.val]).bits≤K) :
    WordsWithin K (negateRowTrace row).events := by
  have negative (q : ℚ) : (Code.ofRat (-q)).bits=(Code.ofRat q).bits := by simp [Code.ofRat,Code.bits]
  apply Weights.materialize_words _ _ _ indices
  · intro j
    have index : j.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
    simpa [Traced.bind_events,Traced.bind_value,readRat,emit,negative,wordsWithin_append,wordsWithin_cons,
      wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp] using
      And.intro (And.intro index (cells j)) (And.intro (cells j) (cells j))
  · intro j
    simpa [Traced.bind_value,readRat,emit,negative] using cells j

def fixTrace (input : Stored (n:=n) (m:=m)) (row : Vector ℚ n) (value : ℚ) :
    Traced (Stored (n:=n) (m:=m+1+1)) := do
  let first ← addCutTrace input row value
  let opposite ← negateRowTrace row
  let negative ← emit .ratNeg [(Code.ofRat value).bits,(Code.ofRat (-value)).bits] (-value)
  addCutTrace first opposite negative

@[simp] theorem fixTrace_value (input : Stored (n:=n) (m:=m)) (row : Vector ℚ n) (value : ℚ) :
    (fixTrace input row value).value=input.fix row value := by
  simp [fixTrace,Traced.bind_value,Stored.fix]

theorem fixTrace_count (input : Stored (n:=n) (m:=m)) (row : Vector ℚ n) (value : ℚ) :
    (fixTrace input row value).events.length≤(2*m+1)*(3*n+13)+4*n+12 := by
  have first := addCutTrace_count input row value
  have second := addCutTrace_count (input.addCut row value) (row.map (-·)) (-value)
  have neg := negateRowTrace_count row
  simp only [fixTrace,Traced.bind_events,Traced.bind_value,addCutTrace_value,negateRowTrace_value,
    emit_value,emit_length,List.length_append]
  nlinarith

def withObjectiveTrace (input : Stored (n:=n) (m:=m)) (objective : Vector ℚ n) : Traced (Stored (n:=n) (m:=m)) := do
  let copied ← copyRatVector objective
  emit .write [n.size,m.size] (input.withObjective copied)

@[simp] theorem withObjectiveTrace_value (input : Stored (n:=n) (m:=m)) (objective : Vector ℚ n) :
    (withObjectiveTrace input objective).value=input.withObjective objective := by
  simp [withObjectiveTrace,Traced.bind_value]

theorem withObjectiveTrace_count (input : Stored (n:=n) (m:=m)) (objective : Vector ℚ n) :
    (withObjectiveTrace input objective).events.length≤3*n+2 := by
  have copied := copyRatVector_count objective
  simp only [withObjectiveTrace,Traced.bind_events,Traced.bind_value,List.length_append,emit_length]
  omega

theorem fixTrace_words (input : Stored (n:=n) (m:=m)) (row : Vector ℚ n) (value : ℚ) (K : ℕ)
    (indices : n+m+3≤K)
    (coefficients : ∀ i : Fin m, ∀ j : Fin n, (Code.ofRat input.coefficients[i.val][j.val]).bits≤K)
    (bounds : ∀ i : Fin m, (Code.ofRat input.bounds[i.val]).bits≤K)
    (rowbits : ∀ j : Fin n, (Code.ofRat row[j.val]).bits≤K)
    (scalar : (Code.ofRat value).bits≤K) :
    WordsWithin K (fixTrace input row value).events := by
  have negative (q : ℚ) : (Code.ofRat (-q)).bits=(Code.ofRat q).bits := by simp [Code.ofRat,Code.bits]
  have first := addCutTrace_words input row value K (by omega) coefficients bounds scalar
  have negated := negateRowTrace_words row K (by omega) rowbits
  have next_coefficients : ∀ i : Fin (m+1), ∀ j : Fin n,
      (Code.ofRat (input.addCut row value).coefficients[i.val][j.val]).bits≤K := by
    intro i
    apply Fin.lastCases (motive:=fun i => ∀ j : Fin n,
      (Code.ofRat (input.addCut row value).coefficients[i.val][j.val]).bits≤K) _ _ i
    · intro j; simpa [Stored.addCut] using rowbits j
    · intro i j; simpa [Stored.addCut] using coefficients i j
  have next_bounds : ∀ i : Fin (m+1), (Code.ofRat (input.addCut row value).bounds[i.val]).bits≤K := by
    intro i
    apply Fin.lastCases (motive:=fun i => (Code.ofRat (input.addCut row value).bounds[i.val]).bits≤K) _ _ i
    · simpa [Stored.addCut] using scalar
    · intro i; simpa [Stored.addCut] using bounds i
  have second := addCutTrace_words (input.addCut row value) (row.map (-·)) (-value) K
    (by omega) next_coefficients next_bounds (by simpa [negative] using scalar)
  simpa only [fixTrace,Traced.bind_events,Traced.bind_value,addCutTrace_value,negateRowTrace_value,emit,
    wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,
    forall_eq_or_imp,forall_eq,and_true,negative] using
    And.intro first (And.intro negated (And.intro (And.intro scalar scalar) second))

theorem withObjectiveTrace_words (input : Stored (n:=n) (m:=m)) (objective : Vector ℚ n) (K : ℕ)
    (indices : n+m≤K) (cells : ∀ j : Fin n, (Code.ofRat objective[j.val]).bits≤K) :
    WordsWithin K (withObjectiveTrace input objective).events := by
  have copied := copyRatVector_words objective K (by omega) cells
  have nsize : n.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have msize : m.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  simpa only [withObjectiveTrace,Traced.bind_events,Traced.bind_value,emit,wordsWithin_append,wordsWithin_cons,
    wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true] using
    And.intro copied (And.intro nsize msize)

end BuyAtBulk.PolynomialLP
