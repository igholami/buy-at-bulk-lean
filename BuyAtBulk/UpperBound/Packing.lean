import BuyAtBulk.UpperBound.HelperSelection
import BuyAtBulk.UpperBound.PackingSums
import BuyAtBulk.UpperBound.TollSeparation

/-! Heavy/light accounting for the exact coefficient in Lemma 4.6. Separation
is a separately proved graph fact; run-trace instantiation is required. -/
noncomputable section
namespace BuyAtBulk.Packing

variable {V R I : Type} [Fintype V] [Fintype R] [Fintype I]
local instance packingLocalInst1 : DecidableEq V := Classical.decEq V
local instance packingLocalInst2 : DecidableEq I := Classical.decEq I

/-- The source's constant-coefficient inequality for actual row data, once
chronological birth separation has been established on the bought helper. -/
theorem packing_from_separated_rows (D : Helper.TollData V R) (h : ℕ) (hh : 0 < h)
    (budget_pos : 0 < D.budget) (row_count : Fintype.card R ≤ (8 * h) ^ 2)
    (selection : Helper.Selection D h)
    (birth : I → R) (radius : ℚ) (uniform_radius : ∀ i, D.radius (birth i) = radius)
    (separated : ∀ v ∈ selection.nodes, ∀ i j : I, i ≠ j →
      ¬ (0 < D.toll (birth i) v ∧ 0 < D.toll (birth j) v)) :
    (16 * radius) * Fintype.card I ≤ (1664 / 3 : ℚ) * D.budget := by
  classical
  let heavy : Finset I := Finset.univ.filter fun i => ¬ D.lightRow h (birth i)
  let light : Finset I := Finset.univ.filter fun i => D.lightRow h (birth i)
  let selected := selection.nodes \ D.heavy h
  have heavy_le_budget : (∑ v ∈ D.heavy h, D.opening v * D.buying v) ≤ D.budget := by
    calc
      _ ≤ ∑ v, D.opening v * D.buying v := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro v _ _
        exact mul_nonneg (D.opening_nonneg v) (D.buying_nonneg v)
      _ = _ := by unfold Helper.TollData.budget; apply Finset.sum_congr rfl; intros; ring
  have heavy_lower : (3 * radius / 8) * (heavy.card : ℚ) ≤
      ∑ i ∈ heavy, ∑ v ∈ D.heavy h, D.opening v * D.toll (birth i) v := by
    calc
      _ = ∑ i ∈ heavy, (3 * radius / 8) := by simp [mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : ¬ D.lightRow h (birth i) := (Finset.mem_filter.mp hi).2
        have hle := not_lt.mp hi'
        change 3 * D.radius (birth i) / 8 ≤ ∑ v ∈ D.heavy h, D.opening v * D.toll (birth i) v at hle
        simpa [uniform_radius i] using hle
  have heavy_upper := separated_rows_sum_le heavy (D.heavy h) (fun i v => D.toll (birth i) v)
    D.opening D.buying (fun v _ => D.opening_nonneg v) (fun v _ => D.buying_nonneg v)
    (fun i _ v _ => D.toll_nonneg (birth i) v) (fun i _ v _ => D.toll_le_buying (birth i) v)
    (fun v hv i _ j _ hij => separated v (selection.heavy_bought hv) i j hij)
  have heavy_bound : (3 * radius / 8) * (heavy.card : ℚ) ≤ D.budget :=
    heavy_lower.trans (heavy_upper.trans heavy_le_budget)
  have cover := selection.light_cover
  have light_lower : (Helper.TollData.alpha h * radius / 8) * (light.card : ℚ) ≤
      ∑ i ∈ light, ∑ v ∈ selected, D.toll (birth i) v := by
    calc
      _ = ∑ i ∈ light, (Helper.TollData.alpha h * radius / 8) := by simp [mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        have hl := cover (birth i) (Finset.mem_filter.mp hi).2
        simpa [uniform_radius i, selected] using hl.le
  have light_upper := separated_rows_sum_le light selected (fun i v => D.toll (birth i) v)
    (fun _ => 1) D.buying (fun _ _ => by norm_num) (fun v _ => D.buying_nonneg v)
    (fun i _ v _ => D.toll_nonneg (birth i) v) (fun i _ v _ => D.toll_le_buying (birth i) v)
    (fun v hv i _ j _ hij => separated v (Finset.mem_sdiff.mp hv).1 i j hij)
  simp only [one_mul] at light_upper
  have selected_cost : (∑ v ∈ selected, D.buying v) ≤ 4 * Helper.TollData.alpha h * D.budget := by
    apply le_trans ?_ selection.buying_lt.le
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
    intro v _ _
    exact D.buying_nonneg v
  have light_bound_scaled := light_lower.trans (light_upper.trans selected_cost)
  have light_bound : (radius / 8) * (light.card : ℚ) ≤ 4 * D.budget := by
    by_contra hn
    have hstrict := mul_lt_mul_of_pos_left (lt_of_not_ge hn) (Helper.TollData.alpha_pos h hh)
    have hscaled : Helper.TollData.alpha h * ((radius / 8) * (light.card : ℚ)) ≤
        Helper.TollData.alpha h * (4 * D.budget) := by
      convert light_bound_scaled using 1 <;> ring
    exact (not_lt_of_ge hscaled) hstrict
  have card_identity : (heavy.card : ℚ) + (light.card : ℚ) = Fintype.card I := by
    have hn := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset I))
      (p := fun i => D.lightRow h (birth i))
    dsimp [heavy, light]
    exact_mod_cast (by simpa [add_comm] using hn :
      (Finset.univ.filter fun i => ¬D.lightRow h (birth i)).card +
      (Finset.univ.filter fun i => D.lightRow h (birth i)).card = Fintype.card I)
  rw [← card_identity]
  nlinarith

end BuyAtBulk.Packing
