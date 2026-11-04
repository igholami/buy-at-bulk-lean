import BuyAtBulk.UpperBound.Optimization.Parameters
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity

namespace BuyAtBulk.UpperBound.Optimization

/-- A uniform explicit version of the source's asymptotic candidate. The
inequality `log T ≤ 2 sqrt T` avoids an unformalized 'sufficiently large' cutoff. -/
theorem ceil_log_candidate (T : ℝ) (hT : 1 < T) :
    2 ≤ ⌈4 * T / Real.log T⌉₊ ∧
      T ≤ (⌈4 * T / Real.log T⌉₊ : ℝ) * Real.log ⌈4 * T / Real.log T⌉₊ := by
  let j : ℕ := ⌈4 * T / Real.log T⌉₊
  have hTpos : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hlogle : Real.log T ≤ T := Real.log_le_self hTpos.le
  have hceil : 4 * T / Real.log T ≤ (j : ℝ) := Nat.le_ceil _
  have hfour : 4 ≤ 4 * T / Real.log T := (le_div_iff₀ hlog).mpr (by linarith)
  have hjfour : (4 : ℝ) ≤ j := hfour.trans hceil
  have hjtwo : 2 ≤ j := by exact_mod_cast (show (2 : ℝ) ≤ j by linarith)
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTpos
  have hsquare := Real.sq_sqrt hTpos.le
  have hlogroot : Real.log T ≤ 2 * Real.sqrt T := by
    have hp := Real.log_le_rpow_div hTpos.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at hp
    nlinarith
  have hrootCandidate : 2 * Real.sqrt T ≤ 4 * T / Real.log T :=
    (le_div_iff₀ hlog).mpr (by nlinarith)
  have hjroot : Real.sqrt T ≤ (j : ℝ) := by linarith [hrootCandidate.trans hceil]
  have hlogj := Real.log_le_log hs hjroot
  rw [Real.sqrt_eq_rpow, Real.log_rpow hTpos] at hlogj
  have hbudget : 4 * T ≤ (j : ℝ) * Real.log T := (div_le_iff₀ hlog).mp hceil
  have hprod := mul_le_mul_of_nonneg_left hlogj (show (0 : ℝ) ≤ j by positivity)
  exact ⟨hjtwo, by dsimp [j] at *; nlinarith⟩

/-- The exact minimal integer parameter is bounded without any finite-case
assumption beyond `log(2h)>1`. -/
theorem q_le_log_two_h {h : ℕ} (hT : 1 < Real.log (2 * (h : ℝ))) :
    (q h : ℝ) ≤ 5 * Real.log (2 * (h : ℝ)) /
      Real.log (Real.log (2 * (h : ℝ))) := by
  let T := Real.log (2 * (h : ℝ))
  let j : ℕ := ⌈4 * T / Real.log T⌉₊
  obtain ⟨hj, hprod⟩ := ceil_log_candidate T hT
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hhpos : (0 : ℝ) < 2 * h := by
    by_contra hn
    have hzle : h ≤ 0 := by exact_mod_cast (by linarith : (h : ℝ) ≤ 0)
    have hz : h = 0 := by omega
    norm_num [hz] at hT
  have hlogpow : Real.log (2 * (h : ℝ)) ≤ Real.log ((j : ℝ) ^ j) := by
    rw [Real.log_pow]
    exact hprod
  have hpowr : 2 * (h : ℝ) ≤ (j : ℝ) ^ j :=
    (Real.log_le_log_iff hhpos (pow_pos hjpos _)).mp hlogpow
  have hpow : 2 * h ≤ j ^ j := by exact_mod_cast hpowr
  have hqj : (q h : ℝ) ≤ j := by exact_mod_cast (q_le hj hpow)
  have hlogT : 0 < Real.log T := Real.log_pos hT
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 4 * T / Real.log T by positivity)
  have hunit : 1 ≤ T / Real.log T :=
    (le_div_iff₀ hlogT).mpr (by simpa using Real.log_le_self (by linarith : 0 ≤ T))
  change (q h : ℝ) ≤ 5 * T / Real.log T
  calc
    (q h : ℝ) ≤ (j : ℝ) := hqj
    _ ≤ 4 * T / Real.log T + 1 := hceil.le
    _ ≤ 4 * T / Real.log T + T / Real.log T := add_le_add le_rfl hunit
    _ = 5 * T / Real.log T := by ring

/-- Uniform logarithmic parameter bound for every source instance with `h≥3`. -/
theorem q_le_log_ratio {h : ℕ} (hh : 3 ≤ h) :
    (q h : ℝ) ≤ 10 * Real.log h / Real.log (Real.log h) := by
  have hhreal : (3 : ℝ) ≤ h := by exact_mod_cast hh
  have hhpos : (0 : ℝ) < h := by linarith
  have hlogh : 1 < Real.log h :=
    (Real.lt_log_iff_exp_lt hhpos).mpr (Real.exp_one_lt_three.trans_le hhreal)
  have hlogtwo : Real.log 2 ≤ Real.log h := Real.log_le_log (by norm_num) (by linarith)
  have hT : Real.log (2 * (h : ℝ)) = Real.log 2 + Real.log h :=
    Real.log_mul (by norm_num) hhpos.ne'
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hTlarge : 1 < Real.log (2 * (h : ℝ)) := by rw [hT]; linarith
  have hdenompos : 0 < Real.log (Real.log h) := Real.log_pos hlogh
  have hdenomTpos := Real.log_pos hTlarge
  have hdenom : Real.log (Real.log h) ≤ Real.log (Real.log (2 * (h : ℝ))) :=
    Real.log_le_log (by linarith) (by rw [hT]; linarith)
  have hratio : Real.log (2 * (h : ℝ)) / Real.log (Real.log (2 * (h : ℝ))) ≤
      (2 * Real.log h) / Real.log (Real.log h) := calc
    _ ≤ (2 * Real.log h) / Real.log (Real.log (2 * (h : ℝ))) :=
      div_le_div_of_nonneg_right (by rw [hT]; linarith) hdenomTpos.le
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hdenompos hdenom
  have hq := q_le_log_two_h hTlarge
  calc
    (q h : ℝ) ≤ 5 * Real.log (2 * (h : ℝ)) / Real.log (Real.log (2 * (h : ℝ))) := hq
    _ = 5 * (Real.log (2 * (h : ℝ)) / Real.log (Real.log (2 * (h : ℝ)))) := by ring
    _ ≤ 5 * ((2 * Real.log h) / Real.log (Real.log h)) :=
      mul_le_mul_of_nonneg_left hratio (by norm_num)
    _ = _ := by ring

end BuyAtBulk.UpperBound.Optimization
