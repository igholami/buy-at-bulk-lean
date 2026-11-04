import BuyAtBulk.UpperBound.HelperBudgets
import BuyAtBulk.UpperBound.HelperEstimates

noncomputable section
namespace BuyAtBulk.Helper.TollData

variable {V R : Type} [Fintype V] [Fintype R] (D : TollData V R)

def initialPotential (h : ℕ) : ℚ :=
  ConditionalExpectation.potential D.buying (D.probability h) D.factor (D.amplitude h)
    (D.fixedCost h) (4 * alpha h * D.budget) [] D.vertexOrder

theorem initialPotential_eq (h : ℕ) : D.initialPotential h =
    (D.fixedCost h + ∑ v, D.probability h v * D.buying v) / (4 * alpha h * D.budget) +
      ∑ r, D.amplitude h r * ∏ v, (1 - D.probability h v + D.probability h v * D.factor r v) := by
  classical
  have sum_eq (f : V → ℚ) : (D.vertexOrder.map f).sum = ∑ v, f v := by
    rw [← List.sum_toFinset f D.vertexOrder_nodup, D.vertexOrder_toFinset]
  have prod_eq (f : V → ℚ) : (D.vertexOrder.map f).prod = ∏ v, f v := by
    rw [← List.prod_toFinset f D.vertexOrder_nodup, D.vertexOrder_toFinset]
  simp only [initialPotential, ConditionalExpectation.potential,
    List.map_nil, List.sum_nil, List.prod_nil, add_zero, mul_one]
  simp_rw [sum_eq, prod_eq]

omit [Fintype V] [Fintype R] in
theorem amplification_eq (h : ℕ) : (2 : ℝ) ^ (16 * repetitions h) =
    Real.exp ((alpha h : ℝ) * Real.log 2 / 8) := by
  calc
    _ = Real.exp (((16 * repetitions h : ℕ) : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ = _ := by
      congr 1
      norm_num [alpha]
      <;> ring

theorem initial_row_bound (h : ℕ) (hh : 0 < h) (r : R) :
    ((D.amplitude h r * ∏ v, (1 - D.probability h v + D.probability h v * D.factor r v) : ℚ) : ℝ) ≤
      Real.exp (-(alpha h : ℝ) / 16) := by
  classical
  by_cases light : D.lightRow h r
  · have t_nonneg : ∀ v ∈ (Finset.univ : Finset V), (0 : ℝ) ≤ (D.toll r v : ℝ) / (D.radius r : ℝ) := by
      intro v _
      exact div_nonneg (by exact_mod_cast D.toll_nonneg r v) (by exact_mod_cast (D.radius_pos r).le)
    have t_le : ∀ v ∈ (Finset.univ : Finset V), (D.toll r v : ℝ) / (D.radius r : ℝ) ≤ 1 := by
      intro v _
      apply (div_le_one (by exact_mod_cast D.radius_pos r)).mpr
      exact_mod_cast D.toll_le_radius r v
    have prob_nonneg : ∀ v ∈ (Finset.univ : Finset V), (0 : ℝ) ≤ (D.probability h v : ℝ) := by
      intro v _
      exact_mod_cast (D.probability_bounds h v).1
    have prob_le : ∀ v ∈ (Finset.univ : Finset V), (D.probability h v : ℝ) ≤ 1 := by
      intro v _
      exact_mod_cast (D.probability_bounds h v).2
    have mass : 3 * (alpha h : ℝ) / 8 ≤
        ∑ v, (D.probability h v : ℝ) * ((D.toll r v : ℝ) / (D.radius r : ℝ)) := by
      exact_mod_cast D.light_probability_mass h hh r light
    have hb := HelperEstimates.expected_row_bound Finset.univ
      (fun v => (D.toll r v : ℝ) / (D.radius r : ℝ))
      (fun v => (D.probability h v : ℝ)) (alpha h : ℝ)
      (by exact_mod_cast (alpha_pos h hh).le) t_nonneg t_le prob_nonneg prob_le mass
    have product_eq : (∏ v, ((1 - D.probability h v + D.probability h v * D.factor r v : ℚ) : ℝ)) =
        ∏ v, (1 - (D.probability h v : ℝ) * ((D.toll r v : ℝ) / (D.radius r : ℝ)) / 2) := by
      apply Finset.prod_congr rfl
      intro v _
      unfold factor
      push_cast
      have hr : (D.radius r : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast D.radius_pos r)
      field_simp
      <;> ring
    simp only [amplitude, if_pos light, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_prod]
    rw [product_eq, amplification_eq]
    exact hb
  · simp only [amplitude, if_neg light, zero_mul, Rat.cast_zero]
    exact (Real.exp_pos _).le

theorem initialPotential_lt_half (h : ℕ) (hh : 0 < h)
    (budget_pos : 0 < D.budget) (row_count : Fintype.card R ≤ (8 * h) ^ 2) :
    D.initialPotential h < 1 / 2 := by
  have ha := alpha_pos h hh
  have normalization_pos : 0 < 4 * alpha h * D.budget := by positivity
  have cost_le : (D.fixedCost h + ∑ v, D.probability h v * D.buying v) /
      (4 * alpha h * D.budget) ≤ 1 / 4 := by
    apply (div_le_iff₀ normalization_pos).mpr
    have hcost := D.initial_cost_le h
    nlinarith
  have rows_le := Finset.sum_le_sum (s := Finset.univ) fun r _ => D.initial_row_bound h hh r
  have hrows : ((∑ r, D.amplitude h r *
      ∏ v, (1 - D.probability h v + D.probability h v * D.factor r v) : ℚ) : ℝ) ≤
      (Fintype.card R : ℝ) * Real.exp (-(alpha h : ℝ) / 16) := by
    simpa using rows_le
  have hn : 2 ≤ repetitions h := by
    by_contra hn
    have hn' : repetitions h ≤ 1 := by omega
    have hp := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp hn'
    change 8 * h ≤ 2 ^ 1 at hp
    omega
  have hsize : Fintype.card R ≤ (2 ^ repetitions h) ^ 2 := by
    have hp := Nat.le_pow_clog (by decide : 1 < 2) (8 * h)
    exact row_count.trans (Nat.pow_le_pow_left hp 2)
  have htail := HelperEstimates.rowcount_tail (repetitions h) (Fintype.card R) hn hsize
  have htail' : (Fintype.card R : ℝ) * Real.exp (-(alpha h : ℝ) / 16) < 1 / 4 := by
    simpa [alpha] using htail
  have rows_lt : (∑ r, D.amplitude h r *
      ∏ v, (1 - D.probability h v + D.probability h v * D.factor r v)) < (1 / 4 : ℚ) := by
    apply (Rat.cast_lt (K := ℝ)).mp
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    exact hrows.trans_lt htail'
  rw [D.initialPotential_eq]
  linarith

end BuyAtBulk.Helper.TollData
