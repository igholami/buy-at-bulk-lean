import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace BuyAtBulk.UpperBound.Optimization

private theorem exists_q (h : ℕ) : ∃ j : ℕ, 2 ≤ j ∧ 2 * h ≤ j ^ j := by
  refine ⟨2 * h + 2, by omega, ?_⟩
  exact (show 2 * h ≤ 2 * h + 2 by omega).trans (Nat.le_pow (by omega))

/-- Exact integer choice from source equation `eq:cg-4`. -/
noncomputable def q (h : ℕ) : ℕ := Nat.find (exists_q h)

/-- The source's girth parameter. -/
noncomputable def r (h : ℕ) : ℕ := 2 * q h

/-- The source's integer grid ratio. -/
noncomputable def scaleRatio (h : ℕ) : ℕ := max 8 ⌈Real.sqrt (q h)⌉₊

theorem q_spec (h : ℕ) : 2 ≤ q h ∧ 2 * h ≤ q h ^ q h := Nat.find_spec (exists_q h)

theorem q_le {h j : ℕ} (hj : 2 ≤ j) (hpow : 2 * h ≤ j ^ j) : q h ≤ j :=
  Nat.find_min' (exists_q h) ⟨hj, hpow⟩

theorem q_small {h : ℕ} (hh : h ≤ 2) : q h = 2 := by
  have hupper : q h ≤ 2 := q_le (by omega) (by norm_num; omega)
  have hlower := (q_spec h).1
  omega

theorem scaleRatio_lower (h : ℕ) : 8 ≤ scaleRatio h := le_max_left _ _

theorem sqrt_q_le_scaleRatio (h : ℕ) : Real.sqrt (q h) ≤ (scaleRatio h : ℝ) := by
  exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 8 ⌈Real.sqrt (q h)⌉₊)

/-- The large minimum ratio only changes the absolute constant. -/
theorem scaleRatio_upper (h : ℕ) : (scaleRatio h : ℝ) ≤ 8 * Real.sqrt (q h) := by
  have hq : (1 : ℝ) ≤ q h := by exact_mod_cast (show 1 ≤ q h by have := (q_spec h).1; omega)
  have hs : 1 ≤ Real.sqrt (q h) := (Real.one_le_sqrt).mpr hq
  have hceil := Nat.ceil_lt_add_one (Real.sqrt_nonneg (q h))
  have hmax : (scaleRatio h : ℝ) = max 8 (⌈Real.sqrt (q h)⌉₊ : ℝ) := by
    simp [scaleRatio]
  rw [hmax]
  exact max_le (by linarith) (by linarith)

/-- The common scale grid spans the whole request range in at most `2q` jumps. -/
theorem scale_power (h : ℕ) : 2 * h ≤ scaleRatio h ^ (2 * q h) := by
  have hs := sqrt_q_le_scaleRatio h
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ q h by positivity)
  have hsqle : (q h : ℝ) ≤ (scaleRatio h : ℝ) ^ 2 := by
    have hnonneg := Real.sqrt_nonneg (q h)
    nlinarith
  have hnat : q h ≤ scaleRatio h ^ 2 := by exact_mod_cast hsqle
  calc
    2 * h ≤ q h ^ q h := (q_spec h).2
    _ ≤ (scaleRatio h ^ 2) ^ q h := Nat.pow_le_pow_left hnat _
    _ = _ := by rw [← pow_mul]

end BuyAtBulk.UpperBound.Optimization
