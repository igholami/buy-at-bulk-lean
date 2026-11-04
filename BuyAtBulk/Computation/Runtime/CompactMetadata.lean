import BuyAtBulk.Computation.Runtime.CompactLiftWords

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.Computation.Runtime.CompactLift
open Rational BuyAtBulk.PolynomialLP.CompactEncoding
variable {n h : ℕ}

def optionWidth : Option ℚ→ℕ
  | none=>1
  | some q=>(Code.ofRat q).bits+1

def completeScan (values : Vector (Option ℚ) h) : List (Fin h)→Traced Bool
  | []=>⟨true,[⟨.branch,[1]⟩]⟩
  | i::rest=>
    let events : List Event := [⟨.scan,[i.val.size]⟩,⟨.read,[i.val.size,1]⟩,⟨.branch,[1]⟩]
    if values[i.val].isSome then
      let tail := completeScan values rest
      ⟨tail.value,events++tail.events⟩
    else ⟨false,events⟩

theorem completeScan_true (values : Vector (Option ℚ) h) (order : List (Fin h)) :
    (completeScan values order).value=true ↔ ∀ i∈order,values[i.val].isSome=true := by
  induction order with
  | nil=>simp [completeScan]
  | cons i rest ih=>
    simp only [completeScan]
    split <;> simp_all

theorem completeScan_count (values : Vector (Option ℚ) h) (order : List (Fin h)) :
    (completeScan values order).events.length ≤ 3*order.length+1 := by
  induction order with
  | nil=>simp [completeScan]
  | cons i rest ih=>
    simp only [completeScan]
    split <;> simp only [List.length_append,List.length_cons,List.length_nil] <;> omega

theorem completeScan_words (values : Vector (Option ℚ) h) (order : List (Fin h)) (K : ℕ)
    (dimension : h ≤ K) (one : 1 ≤ K) : WordsWithin K (completeScan values order).events := by
  induction order with
  | nil=>simp [completeScan,WordsWithin,one]
  | cons i rest ih=>
    have index : i.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have:=i.isLt;omega)
    simp only [completeScan]
    split <;> simp_all [wordsWithin_append,wordsWithin_cons]

def lengthCell (values : Vector (Option ℚ) h) (valid : ∀ i : Fin h,values[i.val].isSome=true) (i : Fin h) : Traced ℚ :=
  let q := values[i.val].get (valid i)
  emit .read [i.val.size,(Code.ofRat q).bits] q
@[simp] theorem lengthCell_value (values : Vector (Option ℚ) h) (valid : ∀ i : Fin h,values[i.val].isSome=true) (i : Fin h) :
    (lengthCell values valid i).value=values[i.val].get (valid i) := rfl
@[simp] theorem lengthCell_count (values : Vector (Option ℚ) h) (valid : ∀ i : Fin h,values[i.val].isSome=true) (i : Fin h) :
    (lengthCell values valid i).events.length=1 := rfl

def collectPayload (values : Vector (Option ℚ) h) (valid : ∀ i : Fin h,values[i.val].isSome=true) : Traced (Vector ℚ h) :=
  Weights.materialize (lengthCell values valid) (fun q=>(Code.ofRat q).bits)
@[simp] theorem collectPayload_get (values : Vector (Option ℚ) h) (valid : ∀ i : Fin h,values[i.val].isSome=true) (i : Fin h) :
    (collectPayload values valid).value[i.val]=values[i.val].get (valid i) := by
  simp only [collectPayload,Weights.materialize_get,lengthCell_value]
@[simp] theorem collectPayload_count (values : Vector (Option ℚ) h) (valid : ∀ i : Fin h,values[i.val].isSome=true) :
    (collectPayload values valid).events.length=3*h+1 := by
  simp [collectPayload,Weights.materialize,List.length_flatMap,lengthCell_count,Nat.mul_comm]

theorem collectPayload_words (values : Vector (Option ℚ) h) (valid : ∀ i : Fin h,values[i.val].isSome=true)
    (Q K : ℕ) (dimension : h ≤ K) (budget : Q ≤ K)
    (inputs : ∀ i : Fin h,(Code.ofRat (values[i.val].get (valid i))).bits ≤ Q) :
    WordsWithin K (collectPayload values valid).events := by
  apply Weights.materialize_words
  · exact dimension
  · intro i
    have index : i.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have:=i.isLt;omega)
    simp only [lengthCell,emit,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
      or_false,forall_eq_or_imp,forall_eq,and_true]
    exact ⟨index,(inputs i).trans budget⟩
  · intro i
    exact (inputs i).trans budget

def lengths (input : ShortestPath.GraphEncoding n) (physical : Vector ℚ n) (source target : Vector (Fin n) h)
    (point : Vector ℚ (variableCount n h)) : Traced (Option (Vector ℚ h)) :=
  let options := Weights.materialize (commodity input physical source target point) optionWidth
  let indices := indexList h
  let checked := completeScan options.value indices.value
  if success : checked.value=true then
    have valid : ∀ i : Fin h,options.value[i.val].isSome=true := by
      intro i
      exact (completeScan_true options.value indices.value).mp success i (by simp[indices])
    let output := collectPayload options.value valid
    ⟨some output.value,options.events++indices.events++checked.events++[⟨.branch,[1]⟩]++output.events++[⟨.write,[h.size]⟩]⟩
  else ⟨none,options.events++indices.events++checked.events++[⟨.branch,[1]⟩,⟨.write,[1]⟩]⟩

theorem lengths_value (input : ShortestPath.GraphEncoding n) (f : CompactFlow.Solution input.graph h)
    (point : Vector ℚ (variableCount n h)) (coordinates : f.coordinates=decode (fun j=>point[j.val])) :
    (lengths input (Vector.ofFn f.physical) (Vector.ofFn f.source) (Vector.ofFn f.target) point).value=
      some (Vector.ofFn fun i=>FlowDecomposition.fractionalLength input.graph (Equiv.refl _) f i) := by
  have options (i : Fin h) : (Weights.materialize (commodity input (Vector.ofFn f.physical)
      (Vector.ofFn f.source) (Vector.ofFn f.target) point) optionWidth).value[i.val]=
      some (FlowDecomposition.fractionalLength input.graph (Equiv.refl _) f i) := by
    rw [Weights.materialize_get,commodity_value input f point coordinates]
  have checked : (completeScan (Weights.materialize (commodity input (Vector.ofFn f.physical)
      (Vector.ofFn f.source) (Vector.ofFn f.target) point) optionWidth).value (List.finRange h)).value=true := by
    apply (completeScan_true _ _).mpr
    intro i _
    rw [options]
    rfl
  unfold lengths
  simp only [indexList_value,checked,dif_pos]
  congr 1
  apply Vector.ext
  intro i bound
  change (collectPayload _ _).value[(⟨i,bound⟩ : Fin h).val]=_
  rw [collectPayload_get]
  simp only [Vector.getElem_ofFn]
  exact Option.get_of_eq_some _ (options ⟨i,bound⟩)

def lengthsCount (n h : ℕ) := h*(commodityCount n+12)+10

theorem lengths_count (input : ShortestPath.GraphEncoding n) (f : CompactFlow.Solution input.graph h)
    (point : Vector ℚ (variableCount n h)) (coordinates : f.coordinates=decode (fun j=>point[j.val])) :
    (lengths input (Vector.ofFn f.physical) (Vector.ofFn f.source) (Vector.ofFn f.target) point).events.length ≤ lengthsCount n h := by
  have options := Weights.materialize_count (commodity input (Vector.ofFn f.physical)
    (Vector.ofFn f.source) (Vector.ofFn f.target) point) optionWidth (commodityCount n)
    (commodity_count input f point coordinates)
  have checked := completeScan_count (Weights.materialize (commodity input (Vector.ofFn f.physical)
    (Vector.ofFn f.source) (Vector.ofFn f.target) point) optionWidth).value (List.finRange h)
  simp only [List.length_finRange] at checked
  unfold lengths
  dsimp only
  split <;> simp only [List.length_append,List.length_cons,List.length_nil,indexList_count,indexList_value,collectPayload_count]
  all_goals dsimp only [lengthsCount];nlinarith

end BuyAtBulk.Computation.Runtime.CompactLift
