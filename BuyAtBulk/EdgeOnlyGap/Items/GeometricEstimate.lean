import BuyAtBulk.EdgeOnlyGap.Items.WitnessUnionBound

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

private lemma sum_Icc_geom_bound (ρ : ℝ) (g T : ℕ) (hT : g ≤ T) :
    (∑ m ∈ Finset.Icc g T, ρ ^ m) * (1 - ρ) = ρ ^ g - ρ ^ (T + 1) := by
  induction T with
  | zero =>
    have hg : g = 0 := by omega
    subst hg
    simp
    <;> ring
  | succ k ih =>
    by_cases hgk : g ≤ k
    · have hIcc : Finset.Icc g (k + 1) = insert (k + 1) (Finset.Icc g k) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnotmem : k + 1 ∉ Finset.Icc g k := by
        simp only [Finset.mem_Icc]
        omega
      rw [hIcc, Finset.sum_insert hnotmem, add_mul, ih hgk]
      ring
    · have hgk_eq : g = k + 1 := by omega
      subst hgk_eq
      simp
      ring

/-- Pp. 2–3: finite geometric tail and prescribed-q estimates. -/
theorem geometricEstimate (n d g T : ℕ) (hn : 0 < n) (hd : 4 ≤ d)
    (hg : 4 ≤ g) (hT : g ≤ T) :
  let A := (liftA d:ℝ)
  let q := (liftQ n d g T:ℝ)
  let ρ := A * Real.rpow (4*T/q) (2/(g:ℝ))
  4*T/q ≤ A^(-(g:ℤ)) ∧ ρ ≤ 1/A ∧ 1/A < 1/2 ∧
  (n:ℝ)*q * (∑ m ∈ Finset.Icc g T, A^m*Real.rpow (4*T/q) (2*(m:ℝ)/g)) ≤
    n*q*ρ^g/(1-ρ) ∧
  n*q*ρ^g/(1-ρ) ≤ 32*n*T^2*A^g/q ∧
  32*n*T^2*A^g/q ≤ 32/1000 ∧ (32/1000:ℝ)<1 := by
  intro A q ρ
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hg_pos : (0 : ℝ) < g := Nat.cast_pos.mpr (by omega)
  have hT_pos : (0 : ℝ) < T := Nat.cast_pos.mpr (by omega)
  have hA_ge : (1024 : ℝ) ≤ A := by
    change (1024 : ℝ) ≤ (liftA d : ℝ)
    unfold liftA
    push_cast
    have hdR : (4 : ℝ) ≤ d := Nat.ofNat_le_cast.mpr hd
    nlinarith
  have hA_pos : 0 < A := by linarith
  have hAg_pos : 0 < A ^ g := pow_pos hA_pos g
  have hq_eq : q = 1000 * (n : ℝ) * (T : ℝ) ^ 2 * A ^ g := by
    change (liftQ n d g T : ℝ) = _
    unfold liftQ
    push_cast
    ring
  have hq_pos : 0 < q := by rw [hq_eq]; positivity
  have h4Tq_nonneg : 0 ≤ 4 * (T : ℝ) / q := by positivity
  have h1 : 4 * (T : ℝ) / q ≤ A ^ (-(g : ℤ)) := by
    rw [zpow_neg, zpow_natCast, div_le_iff₀ hq_pos, inv_mul_eq_div, le_div_iff₀ hAg_pos, hq_eq]
    have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
    have hT4 : (4 : ℝ) ≤ T := Nat.ofNat_le_cast.mpr (by omega)
    have h4T_le : 4 * (T : ℝ) ≤ 1000 * (n : ℝ) * (T : ℝ) ^ 2 := by nlinarith
    nlinarith
  have h2 : ρ ≤ 1 / A := by
    have hy_pos : 0 < A⁻¹ := inv_pos.mpr hA_pos
    have h_base : 4 * (T : ℝ) / q ≤ (A⁻¹) ^ (g : ℝ) := by
      rw [Real.rpow_natCast, inv_pow, ← zpow_natCast, ← zpow_neg]
      exact h1
    have h_rpow : (4 * (T : ℝ) / q) ^ (2 / (g : ℝ)) ≤ (A⁻¹) ^ 2 := by
      calc
        (4 * (T : ℝ) / q) ^ (2 / (g : ℝ))
          ≤ ((A⁻¹) ^ (g : ℝ)) ^ (2 / (g : ℝ)) :=
            Real.rpow_le_rpow h4Tq_nonneg h_base (by positivity)
        _ = (A⁻¹) ^ ((g : ℝ) * (2 / (g : ℝ))) := by
            rw [← Real.rpow_mul (le_of_lt hy_pos)]
        _ = (A⁻¹) ^ ((2 : ℕ) : ℝ) := by
            congr 1
            have hg_ne : (g : ℝ) ≠ 0 := ne_of_gt hg_pos
            push_cast
            field_simp [hg_ne]
        _ = (A⁻¹) ^ 2 := Real.rpow_natCast A⁻¹ 2
    calc
      ρ = A * (4 * (T : ℝ) / q) ^ (2 / (g : ℝ)) := rfl
      _ ≤ A * (A⁻¹) ^ 2 := mul_le_mul_of_nonneg_left h_rpow (le_of_lt hA_pos)
      _ = 1 / A := by
        have hA_ne : A ≠ 0 := ne_of_gt hA_pos
        field_simp [hA_ne]
  have h3 : 1 / A < 1 / 2 := by
    rw [div_lt_div_iff₀ hA_pos (by norm_num)]
    linarith
  have hρ_nonneg : 0 ≤ ρ := by
    change 0 ≤ A * (4 * (T : ℝ) / q) ^ (2 / (g : ℝ))
    positivity
  have h1mρ_pos : 0 < 1 - ρ := by linarith
  have h_term : ∀ m : ℕ, A ^ m * (4 * (T : ℝ) / q) ^ (2 * (m : ℝ) / (g : ℝ)) = ρ ^ m := by
    intro m
    change A ^ m * (4 * (T : ℝ) / q) ^ (2 * (m : ℝ) / (g : ℝ)) =
      (A * (4 * (T : ℝ) / q) ^ (2 / (g : ℝ))) ^ m
    rw [mul_pow, ← Real.rpow_natCast ((4 * (T : ℝ) / q) ^ (2 / (g : ℝ))) m, ← Real.rpow_mul h4Tq_nonneg]
    congr 2
    ring
  have h4 : (n : ℝ) * q * (∑ m ∈ Finset.Icc g T, A ^ m * (4 * (T : ℝ) / q) ^ (2 * (m : ℝ) / (g : ℝ))) ≤
      (n : ℝ) * q * ρ ^ g / (1 - ρ) := by
    have hsum_eq : (∑ m ∈ Finset.Icc g T, A ^ m * (4 * (T : ℝ) / q) ^ (2 * (m : ℝ) / (g : ℝ))) =
        ∑ m ∈ Finset.Icc g T, ρ ^ m :=
      Finset.sum_congr rfl fun m _ => h_term m
    rw [hsum_eq, le_div_iff₀ h1mρ_pos, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [sum_Icc_geom_bound ρ g T hT]
    have hpow_nonneg : 0 ≤ ρ ^ (T + 1) := pow_nonneg hρ_nonneg _
    linarith
  have hρg : ρ ^ g = 16 * (T : ℝ) ^ 2 * A ^ g / q ^ 2 := by
    rw [← h_term g]
    have hg_ne : (g : ℝ) ≠ 0 := ne_of_gt hg_pos
    have hexp : 2 * (g : ℝ) / (g : ℝ) = (2 : ℕ) := by
      push_cast
      field_simp [hg_ne]
    rw [hexp, Real.rpow_natCast]
    ring
  have h5 : (n : ℝ) * q * ρ ^ g / (1 - ρ) ≤ 32 * (n : ℝ) * (T : ℝ) ^ 2 * A ^ g / q := by
    rw [div_le_iff₀ h1mρ_pos]
    have h1mρ_ge : (1 / 2 : ℝ) ≤ 1 - ρ := by linarith
    have h_lhs : (n : ℝ) * q * ρ ^ g = 16 * (n : ℝ) * (T : ℝ) ^ 2 * A ^ g / q := by
      rw [hρg]
      have hq_ne : q ≠ 0 := ne_of_gt hq_pos
      field_simp [hq_ne]
    rw [h_lhs]
    have h_nonneg : 0 ≤ 32 * (n : ℝ) * (T : ℝ) ^ 2 * A ^ g / q := by positivity
    calc
      16 * (n : ℝ) * (T : ℝ) ^ 2 * A ^ g / q
        = (32 * (n : ℝ) * (T : ℝ) ^ 2 * A ^ g / q) * (1 / 2) := by ring
      _ ≤ (32 * (n : ℝ) * (T : ℝ) ^ 2 * A ^ g / q) * (1 - ρ) :=
        mul_le_mul_of_nonneg_left h1mρ_ge h_nonneg
  have h6 : 32 * (n : ℝ) * (T : ℝ) ^ 2 * A ^ g / q ≤ 32 / 1000 := by
    rw [hq_eq]
    have h_ne : (n : ℝ) * (T : ℝ) ^ 2 * A ^ g ≠ 0 := ne_of_gt (by positivity)
    have h_eq : 32 * (n : ℝ) * (T : ℝ) ^ 2 * A ^ g / (1000 * (n : ℝ) * (T : ℝ) ^ 2 * A ^ g) = 32 / 1000 := by
      field_simp [h_ne]
    linarith
  refine ⟨h1, h2, h3, h4, h5, h6, by norm_num⟩

end BuyAtBulk.EdgeOnlyGap
