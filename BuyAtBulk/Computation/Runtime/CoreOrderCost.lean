import BuyAtBulk.Computation.Runtime.CoreOrder

namespace BuyAtBulk.Computation.Runtime.StoredCore.Order
variable {h : ℕ}

@[simp] theorem merge_length (allowance : Vector ℚ h) (left right : List (Fin h)) :
    (merge allowance left right).value.length = left.length+right.length := by
  rw [merge_value,List.length_merge]

@[simp] theorem sort_length (allowance : Vector ℚ h) (fuel : ℕ) (indices : List (Fin h)) :
    (sort allowance fuel indices).value.length = indices.length := by
  induction fuel generalizing indices with
  | zero => rfl
  | succ k ih =>
    match indices with
    | [] => rfl
    | [i] => rfl
    | i::j::rest =>
      simp only[sort,merge_length,ih,splitAt_value,length_value,emit_value]
      simp only [List.splitAt_eq,List.length_take,List.length_drop]
      omega

/-- A coarse polynomial bound for the actual stable-sort recursion, including
length scans, contiguous splitting, and both recursively sorted halves. -/
theorem sort_count (allowance : Vector ℚ h) (fuel : ℕ) (indices : List (Fin h)) :
    (sort allowance fuel indices).events.length ≤ 20*(fuel+1)*(indices.length+1)^2 := by
  induction fuel generalizing indices with
  | zero =>
    simp only[sort,emit,List.length_singleton]
    have positive : 0 < (indices.length+1)^2 := by positivity
    omega
  | succ k ih =>
    match indices with
    | [] => simp [sort,emit] <;> omega
    | [i] => simp [sort,emit] <;> omega
    | i::j::rest =>
      let xs := i::j::rest
      let q := (xs.length+1)/2
      let left := (xs.splitAt q).1
      let right := (xs.splitAt q).2
      have lengths : left.length+right.length=xs.length := by
        simp only[left,right,List.splitAt_eq,List.length_take,List.length_drop]
        omega
      have left_pos : 1 ≤ left.length := by simp only[left,q,xs,List.splitAt_eq,List.length_take,List.length_cons];omega
      have right_pos : 1 ≤ right.length := by simp only[right,q,xs,List.splitAt_eq,List.length_drop,List.length_cons];omega
      have square : (left.length+1)^2+(right.length+1)^2 ≤ (xs.length+1)^2 := by nlinarith
      have L := ih left
      have R := ih right
      have S := splitAt_count q xs
      have M := merge_count allowance (sort allowance k left).value (sort allowance k right).value
      simp only[sort_length] at M
      have result := Nat.add_le_add L R
      have totalSquare := Nat.mul_le_mul_left (20*(k+1)) square
      simp only[sort,List.length_append,List.length_cons,List.length_nil,length_value,emit_length,emit_value,
        length_count,splitAt_value]
      change 1+(2*xs.length+1)+1+1+(splitAt q xs).events.length+
        (sort allowance k left).events.length+(sort allowance k right).events.length+
        (merge allowance (sort allowance k left).value (sort allowance k right).value).events.length ≤
        20*(k+1+1)*(xs.length+1)^2
      nlinarith

end BuyAtBulk.Computation.Runtime.StoredCore.Order
