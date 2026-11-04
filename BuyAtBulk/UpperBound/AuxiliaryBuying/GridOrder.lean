import BuyAtBulk.UpperBound.FiniteGrid

namespace BuyAtBulk.UpperBound

/-- Strict common-grid order for positive fractional buying budget. -/
theorem gridScale_strictAnti (budget : ℚ) (budget_pos : 0 < budget)
    (ratio : ℕ) (ratio_ge : 2 ≤ ratio) : StrictAnti (gridScale budget ratio) := by
  intro small large hdepth
  have hr : (1 : ℚ) < ratio := by exact_mod_cast (show 1 < ratio by omega)
  have hrpos : (0 : ℚ) < ratio := by linarith
  unfold gridScale
  apply (div_lt_div_iff₀ (pow_pos hrpos large) (pow_pos hrpos small)).mpr
  exact mul_lt_mul_of_pos_left (pow_lt_pow_right₀ hr hdepth) (by positivity)

theorem gridScale_le_iff_depth_le (budget : ℚ) (budget_pos : 0 < budget)
    (ratio : ℕ) (ratio_ge : 2 ≤ ratio) (first second : ℕ) :
    gridScale budget ratio first ≤ gridScale budget ratio second ↔ second ≤ first :=
  by
    constructor
    · intro hscale
      by_contra hdepth
      have hlt : first < second := by omega
      have hstrict := gridScale_strictAnti budget budget_pos ratio ratio_ge hlt
      linarith
    · intro hdepth
      exact gridScale_antitone_depth budget ratio second first budget_pos.le
        (by omega) (by omega) hdepth

end BuyAtBulk.UpperBound
