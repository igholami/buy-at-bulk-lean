import BuyAtBulk.UpperBound.HelperInitial
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

/-! Exact deterministic helper (Lemma 4.5): the explicit sequential rational
algorithm buys every heavy node, stays within budget and covers every light row.
Polynomial encoding/runtime semantics are a separate computational obligation. -/
noncomputable section
namespace BuyAtBulk.Helper.TollData

variable {V R : Type} [Fintype V] [Fintype R] (D : TollData V R)
local instance helperResultLocalInst1 : DecidableEq V := Classical.decEq V

def rowEstimator (h : ℕ) (r : R) : ℚ :=
  D.amplitude h r * ((D.selected h).map (D.factor r)).prod

def finalPotential (h : ℕ) : ℚ :=
  ConditionalExpectation.potential D.buying (D.probability h) D.factor (D.amplitude h)
    (D.fixedCost h) (4 * alpha h * D.budget) (D.selected h) []

theorem finalPotential_eq (h : ℕ) : D.finalPotential h =
    (∑ v ∈ D.helperSet h, D.buying v) / (4 * alpha h * D.budget) + ∑ r, D.rowEstimator h r := by
  rw [D.helper_buying_identity]
  simp only [finalPotential, ConditionalExpectation.potential, rowEstimator,
    List.map_nil, List.sum_nil, List.prod_nil, add_zero, mul_one]

theorem rowEstimator_nonneg (h : ℕ) (r : R) : 0 ≤ D.rowEstimator h r := by
  apply mul_nonneg
  · unfold amplitude
    split_ifs <;> positivity
  · apply List.prod_nonneg
    intro value hv
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hv
    exact (D.factor_bounds r v).1

theorem finalPotential_lt_half (h : ℕ) (hh : 0 < h)
    (budget_pos : 0 < D.budget) (row_count : Fintype.card R ≤ (8 * h) ^ 2) :
    D.finalPotential h < 1 / 2 :=
  (D.selected_potential_le h).trans_lt (D.initialPotential_lt_half h hh budget_pos row_count)

theorem rowEstimator_le_potential (h : ℕ) (hh : 0 < h) (budget_pos : 0 < D.budget) (r : R) :
    D.rowEstimator h r ≤ D.finalPotential h := by
  have ha := alpha_pos h hh
  have cost_nonneg : 0 ≤ (∑ v ∈ D.helperSet h, D.buying v) / (4 * alpha h * D.budget) :=
    div_nonneg (Finset.sum_nonneg fun v _ => D.buying_nonneg v) (by positivity)
  rw [D.finalPotential_eq]
  have hsum : D.rowEstimator h r ≤ ∑ r, D.rowEstimator h r :=
    Finset.single_le_sum (fun r _ => D.rowEstimator_nonneg h r) (Finset.mem_univ r)
  linarith

theorem helper_cost_lt (h : ℕ) (hh : 0 < h) (budget_pos : 0 < D.budget)
    (row_count : Fintype.card R ≤ (8 * h) ^ 2) :
    (∑ v ∈ D.helperSet h, D.buying v) < 4 * alpha h * D.budget := by
  have ha := alpha_pos h hh
  have norm_pos : 0 < 4 * alpha h * D.budget := by positivity
  have hp := D.finalPotential_lt_half h hh budget_pos row_count
  have nonneg : 0 ≤ ∑ r, D.rowEstimator h r :=
    Finset.sum_nonneg fun r _ => D.rowEstimator_nonneg h r
  rw [D.finalPotential_eq] at hp
  apply (div_lt_one norm_pos).mp
  linarith

theorem failed_row_estimator_ge_one (h : ℕ) (r : R) (light : D.lightRow h r)
    (failed : (∑ v ∈ (D.selected h).toFinset, D.toll r v) ≤ alpha h * D.radius r / 8) :
    1 ≤ D.rowEstimator h r := by
  have ratio_nonneg : ∀ v ∈ (D.selected h).toFinset, (0 : ℝ) ≤
      (D.toll r v : ℝ) / (D.radius r : ℝ) := by
    intro v _
    exact div_nonneg (by exact_mod_cast D.toll_nonneg r v) (by exact_mod_cast (D.radius_pos r).le)
  have ratio_le : ∀ v ∈ (D.selected h).toFinset,
      (D.toll r v : ℝ) / (D.radius r : ℝ) ≤ 1 := by
    intro v _
    apply (div_le_one (by exact_mod_cast D.radius_pos r)).mpr
    exact_mod_cast D.toll_le_radius r v
  have failedQ : (∑ v ∈ (D.selected h).toFinset, D.toll r v / D.radius r) ≤ alpha h / 8 := by
    rw [← Finset.sum_div]
    apply (div_le_iff₀ (D.radius_pos r)).mpr
    nlinarith
  have failedReal : (∑ v ∈ (D.selected h).toFinset,
      (D.toll r v : ℝ) / (D.radius r : ℝ)) ≤ (alpha h : ℝ) / 8 := by exact_mod_cast failedQ
  have he := HelperEstimates.failed_row_estimator (D.selected h).toFinset
    (fun v => (D.toll r v : ℝ) / (D.radius r : ℝ)) (alpha h : ℝ)
    ratio_nonneg ratio_le failedReal
  have identity : (D.rowEstimator h r : ℝ) =
      Real.exp ((alpha h : ℝ) * Real.log 2 / 8) *
        ∏ v ∈ (D.selected h).toFinset, (1 - ((D.toll r v : ℝ) / (D.radius r : ℝ)) / 2) := by
    unfold rowEstimator
    rw [← List.prod_toFinset _ (D.selected_nodup h)]
    simp only [amplitude, if_pos light, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_prod]
    rw [amplification_eq]
    congr 1
    apply Finset.prod_congr rfl
    intro v _
    unfold factor
    push_cast
    field_simp
    <;> ring
  rw [← identity] at he
  exact_mod_cast he

/-- Full mathematical helper conclusion for the actual sequential rational
selection, with the source constants and separate coverage on light nodes. -/
theorem cover_fixed_tolls (h : ℕ) (hh : 0 < h) (budget_pos : 0 < D.budget)
    (row_count : Fintype.card R ≤ (8 * h) ^ 2) :
    D.heavy h ⊆ D.helperSet h ∧
    (∑ v ∈ D.helperSet h, D.buying v) < 4 * alpha h * D.budget ∧
    ∀ r, D.lightRow h r → alpha h * D.radius r / 8 <
      ∑ v ∈ D.helperSet h \ D.heavy h, D.toll r v := by
  refine ⟨Finset.subset_union_left, D.helper_cost_lt h hh budget_pos row_count, ?_⟩
  intro r light
  rw [D.helper_light_eq_selected]
  by_contra hn
  have estimator := D.failed_row_estimator_ge_one h r light (not_lt.mp hn)
  have hle := D.rowEstimator_le_potential h hh budget_pos r
  have hphi := D.finalPotential_lt_half h hh budget_pos row_count
  linarith

end BuyAtBulk.Helper.TollData
