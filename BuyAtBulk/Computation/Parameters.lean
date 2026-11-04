import BuyAtBulk.UpperBound.Optimization.Parameters
import BuyAtBulk.UpperBound.GridLogBridge
import Mathlib.Data.Finset.Sort

/-! Executable exact integer parameter choices. Bounded scans compare integer
powers and squares; no floating-point logarithm or square root is evaluated. -/
namespace BuyAtBulk.Computation.Parameters

def candidates (h : ℕ) : Finset ℕ :=
  (Finset.range (2 * h + 3)).filter fun j => 2 ≤ j ∧ 2 * h ≤ j ^ j

theorem candidates_nonempty (h : ℕ) : (candidates h).Nonempty := by
  refine ⟨2 * h + 2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega, ?_⟩⟩
  exact (show 2 * h ≤ 2 * h + 2 by omega).trans (Nat.le_pow (by omega))

def q (h : ℕ) : ℕ := (candidates h).min' (candidates_nonempty h)
def r (h : ℕ) : ℕ := 2 * q h

theorem q_spec (h : ℕ) : 2 ≤ q h ∧ 2 * h ≤ q h ^ q h :=
  (Finset.mem_filter.mp (Finset.min'_mem (candidates h) (candidates_nonempty h))).2

theorem q_bound (h : ℕ) : q h ≤ 2 * h + 2 := by
  apply Finset.min'_le
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega,
    (show 2 * h ≤ 2 * h + 2 by omega).trans (Nat.le_pow (by omega))⟩

theorem q_eq (h : ℕ) : q h = UpperBound.Optimization.q h := by
  apply le_antisymm
  · apply Finset.min'_le
    have bound : UpperBound.Optimization.q h ≤ 2 * h + 2 :=
      UpperBound.Optimization.q_le (by omega)
        ((show 2 * h ≤ 2 * h + 2 by omega).trans (Nat.le_pow (by omega)))
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), UpperBound.Optimization.q_spec h⟩
  · exact UpperBound.Optimization.q_le (q_spec h).1 (q_spec h).2

def squareCandidates (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 2)).filter fun j => n ≤ j ^ 2

theorem squareCandidates_nonempty (n : ℕ) : (squareCandidates n).Nonempty := by
  refine ⟨n + 1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
  nlinarith

def ceilSqrt (n : ℕ) : ℕ := (squareCandidates n).min' (squareCandidates_nonempty n)

theorem ceilSqrt_spec (n : ℕ) : n ≤ ceilSqrt n ^ 2 :=
  (Finset.mem_filter.mp (Finset.min'_mem (squareCandidates n) (squareCandidates_nonempty n))).2

theorem ceilSqrt_bound (n : ℕ) : ceilSqrt n ≤ n + 1 := by
  apply Finset.min'_le
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by nlinarith⟩

theorem ceilSqrt_eq (n : ℕ) : ceilSqrt n = ⌈Real.sqrt n⌉₊ := by
  have root_nonneg := Real.sqrt_nonneg (n : ℝ)
  have root_sq := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  apply le_antisymm
  · apply Finset.min'_le
    have root_le : Real.sqrt n ≤ (n : ℝ) + 1 := by nlinarith
    have ceil_bound : ⌈Real.sqrt n⌉₊ ≤ n + 1 := Nat.ceil_le.mpr (by exact_mod_cast root_le)
    have ceil_lower : Real.sqrt n ≤ (⌈Real.sqrt n⌉₊ : ℝ) := Nat.le_ceil _
    have square_real : (n : ℝ) ≤ (⌈Real.sqrt n⌉₊ : ℝ) ^ 2 := by nlinarith
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by exact_mod_cast square_real⟩
  · apply Nat.ceil_le.mpr
    have square_real : (n : ℝ) ≤ (ceilSqrt n : ℝ) ^ 2 := by exact_mod_cast ceilSqrt_spec n
    have ceil_nonneg : (0 : ℝ) ≤ ceilSqrt n := Nat.cast_nonneg _
    nlinarith

def scaleRatio (h : ℕ) : ℕ := max 8 (ceilSqrt (q h))
def gridDepth (h ratio : ℕ) : ℕ := Nat.clog ratio (2 * ratio * h)

theorem exact_parameters (h : ℕ) :
    q h = UpperBound.Optimization.q h ∧
    r h = UpperBound.Optimization.r h ∧
    scaleRatio h = UpperBound.Optimization.scaleRatio h ∧
    gridDepth h (scaleRatio h) = Statements.gridLevels h (scaleRatio h) := by
  refine ⟨q_eq h, ?_, ?_, ?_⟩
  · simp only [r, UpperBound.Optimization.r, q_eq]
  · simp only [scaleRatio, UpperBound.Optimization.scaleRatio, ceilSqrt_eq, q_eq]
  · exact UpperBound.gridDepth_eq_gridLevels h (scaleRatio h)

end BuyAtBulk.Computation.Parameters
