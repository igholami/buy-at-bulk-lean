import BuyAtBulk.LowerBound.RequestCount
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.NormNum

namespace BuyAtBulk.LowerBound

/-- The largest admissible unpadded construction size exists for every `h ≥ 2`.
This supplies the integer choice in the source's padding argument; it does not
assert that duplicating graph commodities preserves the fractional optimum. -/
theorem exists_padding_scale (h : ℕ) (hh : 2 ≤ h) :
    ∃ k : ℕ, 1 ≤ k ∧ requestCount k ≤ h ∧ h < requestCount (k + 1) := by
  let P := fun k : ℕ => requestCount k ≤ h
  let k := Nat.findGreatest P h
  have hP1 : P 1 := by simpa [P, requestCount] using hh
  have hkpos : 1 ≤ k := Nat.le_findGreatest (by omega) hP1
  have hkP : requestCount k ≤ h := Nat.findGreatest_spec (by omega) hP1
  refine ⟨k, hkpos, hkP, ?_⟩
  by_contra hn
  have hnext : requestCount (k + 1) ≤ h := by omega
  have hlow := requestCount_lower (k + 1) (by omega)
  have hnextBound : k + 1 ≤ h := by omega
  have hmax : k + 1 ≤ k := Nat.le_findGreatest hnextBound hnext
  omega

end BuyAtBulk.LowerBound
