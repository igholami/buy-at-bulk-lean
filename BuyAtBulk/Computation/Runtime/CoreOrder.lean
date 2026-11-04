import BuyAtBulk.Computation.Runtime.Batch
import BuyAtBulk.UpperBound.CoreRun.Order

/-! Actual stored allowance sort. Contiguous splitting and left-biased merging
match the source stable merge sort, including equal-allowance ties. -/
namespace BuyAtBulk.Computation.Runtime.StoredCore.Order
open Rational
variable {h : ℕ}

def length : List (Fin h) → Traced ℕ
  | [] => emit .branch [1] 0
  | i::rest =>
      let next := length rest
      ⟨next.value+1, [⟨.scan, [i.val.size]⟩] ++ next.events ++ [⟨.natAdd, [next.value.size,1,(next.value+1).size]⟩]⟩

@[simp] theorem length_value (indices : List (Fin h)) : (length indices).value = indices.length := by
  induction indices <;> simp_all [length]

@[simp] theorem length_count (indices : List (Fin h)) : (length indices).events.length = 2*indices.length+1 := by
  induction indices <;> simp_all [length, emit, Nat.mul_add]

def splitAt : ℕ → List (Fin h) → Traced (List (Fin h) × List (Fin h))
  | 0, indices => emit .branch [1] ([], indices)
  | _+1, [] => emit .branch [1] ([], [])
  | k+1, i::rest =>
      let next := splitAt k rest
      ⟨(i::next.value.1,next.value.2), [⟨.scan, [i.val.size]⟩] ++ next.events ++ [⟨.cons, [i.val.size]⟩]⟩

@[simp] theorem splitAt_value (k : ℕ) (indices : List (Fin h)) : (splitAt k indices).value = indices.splitAt k := by
  induction k generalizing indices with
  | zero => simp [splitAt]
  | succ k ih => cases indices <;> simp [splitAt, ih, List.splitAt_eq]

theorem splitAt_count (k : ℕ) (indices : List (Fin h)) : (splitAt k indices).events.length ≤ 2*indices.length+1 := by
  induction k generalizing indices with
  | zero => simp [splitAt, emit]
  | succ k ih => cases indices <;> simp_all [splitAt, emit, Nat.mul_add]

def merge (allowance : Vector ℚ h) : List (Fin h) → List (Fin h) → Traced (List (Fin h))
  | [], right => emit .branch [1] right
  | left, [] => emit .branch [1] left
  | i::left, j::right =>
      let a := readRat allowance i
      let b := readRat allowance j
      let test := ratLe a.value b.value
      let headerEvents :=  a.events++b.events++test.events++[⟨Operation.branch,[1]⟩]
      if test.value then
        let next := merge allowance left (j::right)
        ⟨i::next.value,headerEvents++next.events++[⟨.cons,[i.val.size]⟩]⟩
      else
        let next := merge allowance (i::left) right
        ⟨j::next.value,headerEvents++next.events++[⟨.cons,[j.val.size]⟩]⟩
termination_by left right => left.length+right.length

@[simp] theorem merge_value (allowance : Vector ℚ h) (left right : List (Fin h)) :
    (merge allowance left right).value = left.merge right (fun i j => decide (allowance[i.val] ≤ allowance[j.val])) := by
  fun_induction merge allowance left right <;> simp_all +zetaDelta [merge, List.merge, readRat, ratLe]

theorem merge_count (allowance : Vector ℚ h) (left right : List (Fin h)) :
    (merge allowance left right).events.length ≤ 5*(left.length+right.length)+1 := by
  fun_induction merge allowance left right <;>
    simp_all +zetaDelta only [merge, readRat, emit_value, List.length_append, List.length_cons, List.length_nil,
      ratLe, emit, List.length_singleton] <;> omega

def sort (allowance : Vector ℚ h) : ℕ → List (Fin h) → Traced (List (Fin h))
  | 0, indices => emit .branch [1] indices
  | _+1, [] => emit .branch [1] []
  | _+1, [i] => emit .branch [1] [i]
  | fuel+1, i::j::rest =>
      let size := length (i::j::rest)
      let increment := emit .natAdd [size.value.size,1,(size.value+1).size] (size.value+1)
      let half := emit .intDiv [increment.value.size,2,(increment.value/2).size] (increment.value/2)
      let halves := splitAt half.value (i::j::rest)
      let left := sort allowance fuel halves.value.1
      let right := sort allowance fuel halves.value.2
      let combined := merge allowance left.value right.value
      ⟨combined.value,[⟨.branch,[1]⟩]++size.events++increment.events++half.events++halves.events++left.events++right.events++combined.events⟩

theorem sort_value (allowance : Vector ℚ h) (fuel : ℕ) (indices : List (Fin h)) (enough : indices.length ≤ fuel) :
    (sort allowance fuel indices).value = indices.mergeSort (fun i j => decide (allowance[i.val] ≤ allowance[j.val])) := by
  induction fuel generalizing indices with
  | zero => cases indices <;> simp_all [sort, List.mergeSort]
  | succ k ih =>
      match indices with
      | [] => simp [sort, List.mergeSort, emit]
      | [i] => simp [sort, List.mergeSort, emit]
      | i::j::rest =>
          have left_length : ((i::j::rest).splitAt (((i::j::rest).length+1)/2)).1.length ≤ k := by
            simp only [List.splitAt_eq, List.length_take, List.length_cons] at *
            omega
          have right_length : ((i::j::rest).splitAt (((i::j::rest).length+1)/2)).2.length ≤ k := by
            simp only [List.splitAt_eq, List.length_drop, List.length_cons] at *
            omega
          simp only [sort, length_value, emit_value, splitAt_value, merge_value,
            ih _ left_length, ih _ right_length]
          rw [List.mergeSort]
          rfl

end BuyAtBulk.Computation.Runtime.StoredCore.Order
