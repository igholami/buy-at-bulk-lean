import BuyAtBulk.LowerBound.PaddingScale
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith

namespace BuyAtBulk.LowerBound

/-- The numerical strict inequality in the arbitrary-`h` paragraph of
`thm:node-lower`. The network fractional-optimum and duplicate-request bridges
are separate obligations, so the conclusion is a scale/rate estimate. -/
theorem exists_logarithmic_scale (h : ℕ) (hh : 2 ≤ h) :
    ∃ k : ℕ, 1 ≤ k ∧ requestCount k ≤ h ∧
      (1 / 4 : ℝ) * Real.logb 2 h < ((k : ℝ) + 1) / 2 := by
  obtain ⟨k, hk, hcount, hnext⟩ := exists_padding_scale h hh
  refine ⟨k, hk, hcount, ?_⟩
  have hnat : h < 2 ^ (2 * (k + 1)) := lt_of_lt_of_le hnext (requestCount_upper (k + 1))
  have hpow : (h : ℝ) < (2 : ℝ) ^ (2 * (k + 1)) := by exact_mod_cast hnat
  have hhpos : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) hhpos hpow
  rw [Real.logb_pow] at hlog
  norm_num at hlog
  linarith

end BuyAtBulk.LowerBound
