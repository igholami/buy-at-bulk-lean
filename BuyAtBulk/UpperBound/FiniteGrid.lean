import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! `lem:grid`, using exact integer ceiling logarithms (`Nat.clog`) as required
by the paper's polynomial implementation. The grid is indexed downward:
index d represents the source exponent k=-d. -/
namespace BuyAtBulk.UpperBound

def gridDepth (h ratio : ℕ) : ℕ := Nat.clog ratio (2 * ratio * h)

def binaryDepth (h : ℕ) : ℕ := Nat.clog 2 (2 * h)

def gridScale (budget : ℚ) (ratio depth : ℕ) : ℚ :=
  2 * budget / (ratio : ℚ) ^ depth

def cutoff (budget : ℚ) (h ratio : ℕ) : ℚ := budget / ((ratio : ℚ) * h)

theorem gridDepth_le_binaryDepth (h ratio : ℕ) (ratio_ge : 2 ≤ ratio) :
    gridDepth h ratio ≤ binaryDepth h + 1 := by
  apply (Nat.clog_le_iff_le_pow (show 1 < ratio by omega)).mpr
  have hp := Nat.pow_le_pow_left ratio_ge (binaryDepth h)
  have hb := Nat.le_pow_clog (by decide : 1 < 2) (2 * h)
  change 2 * h ≤ 2 ^ binaryDepth h at hb
  rw [pow_succ]
  nlinarith

theorem binaryDepth_le (h : ℕ) : binaryDepth h ≤ 2 * h := by
  apply Nat.clog_le_of_le_pow
  exact (Nat.lt_pow_self (by decide : 1 < 2)).le

theorem grid_smallest_le_cutoff (budget : ℚ) (h ratio : ℕ)
    (budget_nonneg : 0 ≤ budget) (h_pos : 0 < h) (ratio_ge : 2 ≤ ratio) :
    gridScale budget ratio (gridDepth h ratio) ≤ cutoff budget h ratio := by
  have ratio_pos : 0 < (ratio : ℚ) := by exact_mod_cast (show 0 < ratio by omega)
  have h_pos' : 0 < (h : ℚ) := by exact_mod_cast h_pos
  have hp := Nat.le_pow_clog (show 1 < ratio by omega) (2 * ratio * h)
  have hp' : 2 * (ratio : ℚ) * h ≤ (ratio : ℚ) ^ gridDepth h ratio := by exact_mod_cast hp
  unfold gridScale cutoff
  apply (div_le_div_iff₀ (pow_pos ratio_pos _) (mul_pos ratio_pos h_pos')).mpr
  nlinarith

theorem endpoint_scale_rows_bound (h ratio : ℕ) (h_pos : 0 < h) (ratio_ge : 2 ≤ ratio) :
    2 * h * (gridDepth h ratio + 1) ≤ (8 * h) ^ 2 := by
  have hk := gridDepth_le_binaryDepth h ratio ratio_ge
  have hj := binaryDepth_le h
  nlinarith

theorem active_index_lt_depth (budget : ℚ) (h ratio d : ℕ)
    (budget_nonneg : 0 ≤ budget) (h_pos : 0 < h) (ratio_ge : 2 ≤ ratio)
    (in_grid : d ≤ gridDepth h ratio)
    (active : cutoff budget h ratio < gridScale budget ratio d) :
    d < gridDepth h ratio := by
  have bottom := grid_smallest_le_cutoff budget h ratio budget_nonneg h_pos ratio_ge
  by_contra hn
  have hd : d = gridDepth h ratio := by omega
  subst d
  exact (not_lt_of_ge bottom) active

theorem active_scales_card_bound (budget : ℚ) (h ratio : ℕ)
    (budget_nonneg : 0 ≤ budget) (h_pos : 0 < h) (ratio_ge : 2 ≤ ratio) :
    ((Finset.range (gridDepth h ratio + 1)).filter
      fun d => cutoff budget h ratio < gridScale budget ratio d).card ≤ gridDepth h ratio := by
  calc
    _ ≤ (Finset.range (gridDepth h ratio)).card := by
      apply Finset.card_le_card
      intro d hd
      obtain ⟨hd, active⟩ := Finset.mem_filter.mp hd
      exact Finset.mem_range.mpr (active_index_lt_depth budget h ratio d budget_nonneg h_pos ratio_ge
        (by have := Finset.mem_range.mp hd; omega) active)
    _ = _ := Finset.card_range _

theorem gridScale_antitone_depth (budget : ℚ) (ratio small large : ℕ)
    (budget_nonneg : 0 ≤ budget) (ratio_ge : 1 ≤ ratio) (ratio_pos : 0 < ratio) (depth_le : small ≤ large) :
    gridScale budget ratio large ≤ gridScale budget ratio small := by
  have hr : 1 ≤ (ratio : ℚ) := by exact_mod_cast ratio_ge
  have hrpos : 0 < (ratio : ℚ) := by exact_mod_cast ratio_pos
  unfold gridScale
  apply (div_le_div_iff₀ (pow_pos hrpos large) (pow_pos hrpos small)).mpr
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr depth_le) (by positivity)

theorem active_scale_depth_lt (budget : ℚ) (h ratio d : ℕ)
    (budget_nonneg : 0 ≤ budget) (h_pos : 0 < h) (ratio_ge : 2 ≤ ratio)
    (active : cutoff budget h ratio < gridScale budget ratio d) : d < gridDepth h ratio := by
  by_contra hn
  have depth_le : gridDepth h ratio ≤ d := by omega
  have smaller := gridScale_antitone_depth budget ratio (gridDepth h ratio) d budget_nonneg (by omega) (by omega) depth_le
  have bottom := grid_smallest_le_cutoff budget h ratio budget_nonneg h_pos ratio_ge
  exact (not_lt_of_ge (smaller.trans bottom)) active

end BuyAtBulk.UpperBound
