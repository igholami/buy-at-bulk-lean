import BuyAtBulk.LowerBound.GraphConstruction
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds

namespace BuyAtBulk.LowerBound

/-- Number of requests in the unpadded graph construction. -/
def requestCount (k : ℕ) : ℕ := (2 * k).choose k

/-- The actual terminal-index type has the central binomial cardinality. -/
theorem request_card (k : ℕ) : Fintype.card (Request k) = requestCount k := by
  classical
  simp [Request, requestCount]

/-- Crude lower bound sufficient to bound the search for the largest scale. -/
theorem requestCount_lower (k : ℕ) (hk : 1 ≤ k) : k + 1 ≤ requestCount k := by
  have hle : k + 1 ≤ 2 * k := by omega
  have hchoose := Nat.choose_le_choose k hle
  simpa [requestCount, Nat.choose_succ_self_right] using hchoose

/-- The source's `h_k ≤ 2^(2k)` estimate. -/
theorem requestCount_upper (k : ℕ) : requestCount k ≤ 2 ^ (2 * k) :=
  Nat.choose_le_two_pow (2 * k) k

end BuyAtBulk.LowerBound
