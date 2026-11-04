import BuyAtBulk.UpperBound.GridLogBridge
import BuyAtBulk.UpperBound.HelperData
import Mathlib.Tactic.GCongr

/-! Absolute numerical constants converting the exact core accounting to the
paper's parameterized factors and to the zero-length preprocessing factor. -/
noncomputable section
namespace BuyAtBulk.UpperBound

def coreBuyingFactor (h ratio girthParameter : ℕ) : ℝ :=
  4 * (Helper.TollData.alpha h : ℝ) + (16 / 15 : ℝ) *
    (1 + (1664 / 3 : ℝ) * ((ratio : ℝ) + 1 / 4) * ((ratio : ℝ) / ((ratio : ℝ) - 1)) *
      (gridDepth h ratio) * (1 + (2 * (h : ℝ)) ^ (1 / (girthParameter : ℝ))))

def coreRouteFactor (h ratio girthParameter : ℕ) : ℚ :=
  (2 * (gridDepth h ratio : ℚ) + 1) * (6 * (girthParameter : ℚ) + 6) + 1 / 4

theorem binaryDepth_pos (h : ℕ) (hh : 0 < h) : 0 < binaryDepth h :=
  Nat.clog_pos (by decide) (by omega)

theorem gridDepth_pos (h ratio : ℕ) (hh : 0 < h) (hr : 2 ≤ ratio) : 0 < gridDepth h ratio :=
  Nat.clog_pos (by omega) (by nlinarith)

theorem alpha_le_binary (h : ℕ) (hh : 0 < h) :
    (Helper.TollData.alpha h : ℝ) ≤ 384 * binaryDepth h := by
  have hp := Nat.le_pow_clog (by decide : 1 < 2) (2 * h)
  have power_bound : 8 * h ≤ 2 ^ (binaryDepth h + 2) := by
    rw [pow_add]
    norm_num
    change 8 * h ≤ 2 ^ Nat.clog 2 (2 * h) * 4
    nlinarith
  have hn := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr power_bound
  have hj := binaryDepth_pos h hh
  have hn3 : Nat.clog 2 (8 * h) ≤ 3 * binaryDepth h := by omega
  have hn3Real : (Nat.clog 2 (8 * h) : ℝ) ≤ 3 * (binaryDepth h : ℝ) := by exact_mod_cast hn3
  norm_num [Helper.TollData.alpha, Helper.TollData.repetitions]
  nlinarith

theorem coreBuyingFactor_le (h ratio girthParameter : ℕ) (hh : 0 < h)
    (hr : 8 ≤ ratio) : coreBuyingFactor h ratio girthParameter ≤
      10000 * Statements.buyingFactor h ratio girthParameter := by
  have ha := alpha_le_binary h hh
  have hj : (1 : ℝ) ≤ binaryDepth h := by exact_mod_cast binaryDepth_pos h hh
  have hk : (1 : ℝ) ≤ gridDepth h ratio := by exact_mod_cast gridDepth_pos h ratio hh (by omega)
  have hl : (8 : ℝ) ≤ ratio := by exact_mod_cast hr
  have hu : (0 : ℝ) ≤ 1 + (2 * (h : ℝ)) ^ (1 / (girthParameter : ℝ)) := by positivity
  have hratio : (ratio : ℝ) / ((ratio : ℝ) - 1) ≤ 2 := by
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  have hratio_nonneg : (0 : ℝ) ≤ (ratio : ℝ) / ((ratio : ℝ) - 1) := div_nonneg (by positivity) (by linarith)
  have hlarge : (ratio : ℝ) + 1 / 4 ≤ 2 * ratio := by linarith
  have hlevels : (gridDepth h ratio : ℝ) ≤ 2 * gridDepth h ratio := by linarith
  have hterm : (1664 / 3 : ℝ) * ((ratio : ℝ) + 1 / 4) * ((ratio : ℝ) / ((ratio : ℝ) - 1)) *
      (gridDepth h ratio : ℝ) * (1 + (2 * (h : ℝ)) ^ (1 / (girthParameter : ℝ))) ≤
      (13312 / 3 : ℝ) * ratio * gridDepth h ratio * (1 + (2 * (h : ℝ)) ^ (1 / (girthParameter : ℝ))) := by
    calc
      _ ≤ (1664 / 3 : ℝ) * (2 * ratio) * 2 * (2 * gridDepth h ratio) *
          (1 + (2 * (h : ℝ)) ^ (1 / (girthParameter : ℝ))) := by gcongr
      _ = _ := by ring
  have hproduct : 0 ≤ (ratio : ℝ) * gridDepth h ratio *
      (1 + (2 * (h : ℝ)) ^ (1 / (girthParameter : ℝ))) := by positivity
  unfold coreBuyingFactor Statements.buyingFactor
  rw [← gridDepth_eq_gridLevels, ← binaryDepth_eq_binaryLevels]
  push_cast
  nlinarith

theorem coreRouteFactor_bound (h ratio girthParameter : ℕ) (hh : 0 < h)
    (hratio : 2 ≤ ratio) (hr : 1 ≤ girthParameter) :
    (64 : ℚ) * coreRouteFactor h ratio girthParameter ≤
      2320 * girthParameter * gridDepth h ratio := by
  have hk : (1 : ℚ) ≤ gridDepth h ratio := by exact_mod_cast gridDepth_pos h ratio hh hratio
  have hg : (1 : ℚ) ≤ girthParameter := by exact_mod_cast hr
  have hfirst : 2 * (gridDepth h ratio : ℚ) + 1 ≤ 3 * gridDepth h ratio := by linarith
  have hsecond : 6 * (girthParameter : ℚ) + 6 ≤ 12 * girthParameter := by linarith
  have hmul := mul_le_mul hfirst hsecond (by linarith : (0 : ℚ) ≤ 6 * girthParameter + 6)
    (by positivity : (0 : ℚ) ≤ 3 * gridDepth h ratio)
  have hp : (1 : ℚ) ≤ girthParameter * gridDepth h ratio := by nlinarith [mul_nonneg (sub_nonneg.mpr hg) (sub_nonneg.mpr hk)]
  unfold coreRouteFactor
  nlinarith

theorem zero_length_growth_bound (h : ℕ) (hh : 0 < h) :
    (2 * (h : ℝ)) ^ (1 / (binaryDepth h : ℝ)) ≤ 2 := by
  have hj : (0 : ℝ) < binaryDepth h := by exact_mod_cast binaryDepth_pos h hh
  have hpow : 2 * (h : ℝ) ≤ (2 : ℝ) ^ binaryDepth h := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (2 * h)
  have hg := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 2 * h) hpow (by positivity : (0 : ℝ) ≤ 1 / binaryDepth h)
  have heq : ((2 : ℝ) ^ binaryDepth h) ^ (1 / (binaryDepth h : ℝ)) = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    simp [ne_of_gt hj]
  exact hg.trans_eq heq

theorem zero_length_core_factor_bound (h : ℕ) (hh : 0 < h) :
    coreBuyingFactor h 8 (binaryDepth h) ≤ 490000 * binaryDepth h := by
  have hbase := coreBuyingFactor_le h 8 (binaryDepth h) hh le_rfl
  have hlevels := gridDepth_le_binaryDepth h 8 (by decide)
  have hg := zero_length_growth_bound h hh
  have hj : (1 : ℝ) ≤ binaryDepth h := by exact_mod_cast binaryDepth_pos h hh
  have hk : (gridDepth h 8 : ℝ) ≤ binaryDepth h + 1 := by exact_mod_cast hlevels
  have hku : (gridDepth h 8 : ℝ) * (1 + (2 * (h : ℝ)) ^ (1 / (binaryDepth h : ℝ))) ≤
      3 * ((binaryDepth h : ℝ) + 1) := by
    calc
      _ ≤ (gridDepth h 8 : ℝ) * 3 := mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
      _ ≤ ((binaryDepth h : ℝ) + 1) * 3 := mul_le_mul_of_nonneg_right hk (by norm_num)
      _ = _ := by ring
  unfold Statements.buyingFactor at hbase
  rw [← gridDepth_eq_gridLevels, ← binaryDepth_eq_binaryLevels] at hbase
  norm_num only [Nat.cast_ofNat] at hbase
  nlinarith

end BuyAtBulk.UpperBound
