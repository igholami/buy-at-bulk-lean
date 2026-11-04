import BuyAtBulk.Computation.Runtime.CoreOrderWords

namespace BuyAtBulk.Computation.Runtime.StoredCore
open BuyAtBulk.UpperBound
open Rational
variable {h : ℕ}

def filterActive (active : Vector Bool h) : List (Fin h) → Traced (List (Fin h))
  | [] => emit .branch [1] []
  | i::rest =>
    let tail := filterActive active rest
    let headEvents : List Event := [⟨.scan,[i.val.size]⟩,⟨.read,[i.val.size,1]⟩,⟨.branch,[1]⟩]
    if active[i.val] then
      ⟨i::tail.value,headEvents++tail.events++[⟨.cons,[i.val.size]⟩]⟩
    else ⟨tail.value,headEvents++tail.events⟩

@[simp] theorem filterActive_value (active : Vector Bool h) (indices : List (Fin h)) :
    (filterActive active indices).value=indices.filter (fun i => active[i.val]) := by
  induction indices with
  | nil => rfl
  | cons i rest ih => simp only[filterActive];split_ifs <;>simp_all

theorem filterActive_count (active : Vector Bool h) (indices : List (Fin h)) :
    (filterActive active indices).events.length ≤ 4*indices.length+1 := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
    simp only[filterActive];split_ifs <;>simp only[List.length_append,List.length_cons,List.length_nil] <;>omega

theorem filterActive_words (active : Vector Bool h) (indices : List (Fin h)) :
    WordsWithin (h+1) (filterActive active indices).events := by
  induction indices with
  | nil => simp[filterActive,emit,WordsWithin]
  | cons i rest ih =>
    have ii : i.val.size ≤ h+1 := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := i.isLt;omega)
    have one : 1 ≤ h+1 := by omega
    simp only[filterActive];split_ifs <;>
      simp only[wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
        or_false,forall_eq_or_imp,forall_eq,and_true] <;>aesop

def requestOrder (active : Vector Bool h) (allowance : Vector ℚ h) : Traced (List (Fin h)) := do
  let indices ← indexList h
  let included ← filterActive active indices
  Order.sort allowance h included

theorem requestOrder_value (active : Vector Bool h) (allowance : Vector ℚ h) :
    (requestOrder active allowance).value=CoreRun.requestOrder (StoredState.boughtSet active) (fun i => allowance[i.val]) := by
  have length_bound : ((List.finRange h).filter (fun i => active[i.val])).length ≤ h :=
    (List.length_filter_le _ _).trans_eq (List.length_finRange (n := h))
  simp only[requestOrder,Traced.bind_value,indexList_value,filterActive_value,
    Order.sort_value _ _ _ length_bound,CoreRun.requestOrder]
  congr 1
  apply List.filter_congr
  intro i member
  simp only[StoredState.mem_boughtSet]
  simp

theorem requestOrder_length (active : Vector Bool h) (allowance : Vector ℚ h) :
    (requestOrder active allowance).value.length ≤ h := by
  rw[requestOrder_value]
  exact CoreRun.requestOrder_length_le _ _

def requestOrderCount (h : ℕ) := 3*h+(4*h+1)+20*(h+1)*(h+1)^2

theorem requestOrder_count (active : Vector Bool h) (allowance : Vector ℚ h) :
    (requestOrder active allowance).events.length ≤ requestOrderCount h := by
  have filtered := filterActive_count active (List.finRange h)
  simp only[List.length_finRange] at filtered
  have sorted := Order.sort_count allowance h (filterActive active (List.finRange h)).value
  have length_bound : (filterActive active (List.finRange h)).value.length ≤ h := by
    rw[filterActive_value]
    exact (List.length_filter_le _ _).trans_eq (List.length_finRange (n := h))
  have square := Nat.pow_le_pow_left length_bound 2
  have targetSquare := Nat.pow_le_pow_left (Nat.add_le_add_right length_bound 1) 2
  have product := Nat.mul_le_mul_left (20*(h+1)) targetSquare
  simp only[requestOrder,Traced.bind_events,Traced.bind_value,indexList_value,indexList_count,List.length_append]
  unfold requestOrderCount
  omega

theorem requestOrder_words (active : Vector Bool h) (allowance : Vector ℚ h) (L : ℕ)
    (inputs : ∀ i : Fin h, (Code.ofRat allowance[i.val]).bits ≤ L) :
    WordsWithin (2*h+L+5) (requestOrder active allowance).events := by
  have one : 1 ≤ 2*h+L+5 := by omega
  have indices := indexList_words h (2*h+L+5) (by omega)
  have filtered := (filterActive_words active (List.finRange h)).mono (show h+1 ≤ 2*h+L+5 by omega)
  have sorted := Order.sort_words allowance h (filterActive active (List.finRange h)).value L h inputs (by
    rw[filterActive_value]
    exact (List.length_filter_le _ _).trans_eq (List.length_finRange (n := h)))
  simpa only[requestOrder,Traced.bind_events,Traced.bind_value,indexList_value,wordsWithin_append, Nat.two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using And.intro indices (And.intro filtered sorted)

end BuyAtBulk.Computation.Runtime.StoredCore
