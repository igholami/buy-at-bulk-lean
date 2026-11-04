import BuyAtBulk.Computation.Runtime.OriginalEncodingSize
import BuyAtBulk.Computation.Runtime.OriginalInputSize

/-! The payload measure used by the original-program recurrence is polynomial
in the explicit prefix-coded integer-array input. No coefficient callback or
unencoded input-size parameter occurs in this comparison. -/
set_option autoImplicit false
namespace BuyAtBulk.Computation.Runtime.OriginalEncoding
open Rational BuyAtBulk.Computation.StoredOriginal
open scoped BigOperators
variable {n resources requests : ℕ} (tables : Tables n resources requests)

private theorem index_size (v : Fin n) : v.val.size≤n :=
  (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)

private theorem location_size (location : Fin n ⊕ Sym2 (Fin n)) :
    Original.locationBits location≤2*n+1 := by
  cases location with
  | inl v=>
    have bound := index_size v
    dsimp only[Original.locationBits]
    omega
  | inr edge=>
    have first := index_size (Original.edgePair edge).1
    have second := index_size (Original.edgePair edge).2
    dsimp only[Original.locationBits]
    omega

/-- The stored payload measure is bounded by a fixed polynomial in an actual
binary encoding containing all headers and all stored scalar fields. -/
theorem payload_le_binary : Original.inputSize tables≤16*(inputSize tables+1)^2 := by
  let S := inputSize tables
  have dims : n+resources+requests≤S := dimensions tables
  have cells : n*n+5*resources+3*requests≤S := logical_cells tables
  have endpoints : (∑ i : Fin requests,(tables.source[i.val].val.size+tables.target[i.val].val.size))≤requests*(2*n) := by
    calc
      _ ≤ ∑ _ : Fin requests,2*n := Finset.sum_le_sum fun i _=>by
        have first := index_size tables.source[i.val]
        have second := index_size tables.target[i.val]
        omega
      _ = _ := by simp[Nat.mul_comm]
  have locations : (∑ a : Fin resources,Original.locationBits tables.location[a.val])≤resources*(2*n+1) := by
    calc
      _ ≤ ∑ _ : Fin resources,(2*n+1) := Finset.sum_le_sum fun a _=>location_size _
      _ = _ := by simp[Nat.mul_comm]
  have prices : (∑ a : Fin resources,((Code.ofRat tables.buying[a.val]).bits+(Code.ofRat tables.length[a.val]).bits))≤resources*(2*S) := by
    calc
      _ ≤ ∑ _ : Fin resources,2*S := Finset.sum_le_sum fun a _=>by
        have first := buying_bits tables a
        have second := length_bits tables a
        change _≤2*S
        dsimp[S] at *
        omega
      _ = _ := by simp[Nat.mul_comm]
  have demands : (∑ i : Fin requests,(Code.ofRat tables.demand[i.val]).bits)≤requests*S := by
    calc
      _ ≤ ∑ _ : Fin requests,S := Finset.sum_le_sum fun i _=>demand_bits tables i
      _ = _ := by simp[Nat.mul_comm]
  have eBound : requests*(2*n)≤S*(2*S) := Nat.mul_le_mul (by omega) (by omega)
  have lBound : resources*(2*n+1)≤S*(2*S+1) := Nat.mul_le_mul (by omega) (by omega)
  have pBound : resources*(2*S)≤S*(2*S) := Nat.mul_le_mul_right _ (by omega)
  have dBound : requests*S≤S*S := Nat.mul_le_mul_right _ (by omega)
  dsimp only[Original.inputSize]
  change _≤16*(S+1)^2
  nlinarith

/-- Transfer any fixed power bound from the payload recurrence to actual
binary input length, with constants independent of the supplied instance. -/
theorem polynomial_transfer (C d payload binary : ℕ) (bound : payload≤16*(binary+1)^2) :
    C*(payload+1)^d≤(C*17^d)*(binary+1)^(2*d) := by
  have positive : 1≤(binary+1)^2 := by
    simpa using Nat.pow_le_pow_left (by omega : 1≤binary+1) 2
  have enlarged : payload+1≤17*(binary+1)^2 := by omega
  calc
    _ ≤ C*(17*(binary+1)^2)^d := Nat.mul_le_mul_left C (Nat.pow_le_pow_left enlarged d)
    _ = _ := by rw[mul_pow,pow_mul];ring

theorem payload_polynomial (C d : ℕ) :
    C*(Original.inputSize tables+1)^d≤(C*17^d)*(inputSize tables+1)^(2*d) :=
  polynomial_transfer C d _ _ (payload_le_binary tables)

end BuyAtBulk.Computation.Runtime.OriginalEncoding
