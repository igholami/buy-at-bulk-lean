import BuyAtBulk.UpperBound.HelperData
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace BuyAtBulk.Helper.TollData

variable {V R : Type} [Fintype V] [Fintype R] (D : TollData V R)

local instance helperBudgetsLocalInst1 : DecidableEq V := Classical.decEq V

omit [Fintype R] in
theorem alpha_pos (h : ℕ) (hh : 0 < h) : 0 < alpha h := by
  have hn := Nat.clog_pos (by decide : 1 < 2) (show 1 < 8 * h by omega)
  unfold alpha repetitions
  exact mul_pos (by norm_num) (by exact_mod_cast hn)

theorem factor_bounds (r : R) (v : V) : 0 ≤ D.factor r v ∧ D.factor r v ≤ 1 := by
  have hr := D.radius_pos r
  have hp : 0 < 2 * D.radius r := by positivity
  have hz : 0 ≤ D.toll r v / (2 * D.radius r) := div_nonneg (D.toll_nonneg r v) hp.le
  have hu : D.toll r v / (2 * D.radius r) ≤ 1 / 2 := by
    apply (div_le_iff₀ hp).mpr
    have := D.toll_le_radius r v
    linarith
  unfold factor
  constructor <;> linarith

theorem heavy_indicator_sum (h : ℕ) (f : V → ℚ) :
    (∑ v ∈ D.heavy h, f v) = ∑ v, if v ∈ D.heavy h then f v else 0 := by
  classical
  have heq : D.heavy h = Finset.univ.filter (fun v => v ∈ D.heavy h) := by ext v; simp
  conv_lhs => rw [heq]
  rw [Finset.sum_filter]

theorem initial_cost_le (h : ℕ) :
    D.fixedCost h + (∑ v, D.probability h v * D.buying v) ≤ alpha h * D.budget := by
  classical
  unfold fixedCost budget
  rw [D.heavy_indicator_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : v ∈ D.heavy h
  · have hheavy : 1 ≤ alpha h * D.opening v := by simpa [heavy] using hv
    have h := mul_le_mul_of_nonneg_left hheavy (D.buying_nonneg v)
    simp only [probability, if_pos hv, zero_mul, add_zero]
    nlinarith
  · simp only [probability, if_neg hv, zero_add]
    exact le_of_eq (by ring)

theorem light_probability_mass (h : ℕ) (hh : 0 < h) (r : R) (light : D.lightRow h r) :
    3 * alpha h / 8 ≤ ∑ v, D.probability h v * (D.toll r v / D.radius r) := by
  classical
  have identity : (∑ v, D.probability h v * (D.toll r v / D.radius r)) =
      (alpha h / D.radius r) * ((∑ v, D.opening v * D.toll r v) -
        (∑ v ∈ D.heavy h, D.opening v * D.toll r v)) := by
    rw [D.heavy_indicator_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v ∈ D.heavy h <;> simp [probability, hv] <;> ring
  rw [identity]
  have diff : 3 * D.radius r / 8 ≤ (∑ v, D.opening v * D.toll r v) -
      (∑ v ∈ D.heavy h, D.opening v * D.toll r v) := by
    have mass := D.fractional_mass r
    dsimp [lightRow] at light
    linarith
  have hscaled := mul_le_mul_of_nonneg_left diff (div_pos (alpha_pos h hh) (D.radius_pos r)).le
  have heq : (alpha h / D.radius r) * (3 * D.radius r / 8) = 3 * alpha h / 8 := by
    field_simp [ne_of_gt (D.radius_pos r)]
    <;> ring
  rwa [heq] at hscaled

theorem helper_buying_identity (h : ℕ) :
    (∑ v ∈ D.helperSet h, D.buying v) = D.fixedCost h + ((D.selected h).map D.buying).sum := by
  classical
  have hdisjoint : Disjoint (D.heavy h) (D.selected h).toFinset := by
    apply Finset.disjoint_left.mpr
    intro v hh hv
    exact D.selected_not_heavy h v (List.mem_toFinset.mp hv) hh
  rw [helperSet, Finset.sum_union hdisjoint]
  congr 1
  exact List.sum_toFinset _ (D.selected_nodup h)

theorem helper_light_eq_selected (h : ℕ) :
    D.helperSet h \ D.heavy h = (D.selected h).toFinset := by
  classical
  ext v
  simp only [helperSet, Finset.mem_sdiff, Finset.mem_union, List.mem_toFinset]
  constructor
  · rintro ⟨hv | hv, hn⟩
    · exact False.elim (hn hv)
    · exact hv
  · intro hv
    exact ⟨Or.inr hv, D.selected_not_heavy h v hv⟩

end BuyAtBulk.Helper.TollData
