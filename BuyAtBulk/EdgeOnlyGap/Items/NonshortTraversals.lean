import BuyAtBulk.EdgeOnlyGap.Items.RoutingStatistics

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Equation (8), p. 4. -/
theorem nonshortTraversals (H : FiniteGraph) (q d g : ℕ) (π : Lift H q) (hd : 0 < d)
    (hg : 4 ≤ g) (r : (supplyData H q d π hd).toInstance.IntegralRouting) :
  (requests H - shortCount H q d g π hd r : ℚ) ≤
    (totalCore H q d π hd r : ℚ) / (g-1 : ℕ) := by
  classical
  let S := Finset.univ.filter fun i : Fin (requests H) => coreTraversals H q d π hd r i < g - 1
  let Sc := Finset.univ.filter fun i : Fin (requests H) => ¬ (coreTraversals H q d π hd r i < g - 1)
  have hcard : requests H - shortCount H q d g π hd r = Sc.card := by
    have h1 : S.card + Sc.card = (Finset.univ : Finset (Fin (requests H))).card :=
      Finset.card_filter_add_card_filter_not _
    rw [Finset.card_univ, Fintype.card_fin] at h1
    change requests H - S.card = Sc.card
    omega
  have hsum : Sc.card * (g - 1) ≤ totalCore H q d π hd r := by
    calc Sc.card * (g - 1)
      _ = ∑ _ ∈ Sc, (g - 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ i ∈ Sc, coreTraversals H q d π hd r i := by
        refine Finset.sum_le_sum fun i hi => ?_
        simp only [Sc, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
        exact hi
      _ ≤ ∑ i : Fin (requests H), coreTraversals H q d π hd r i :=
        Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
      _ = totalCore H q d π hd r := rfl
  have hle_sub : shortCount H q d g π hd r ≤ requests H := by
    calc shortCount H q d g π hd r ≤ (Finset.univ : Finset (Fin (requests H))).card :=
          Finset.card_filter_le _ _
      _ = requests H := by simp
  have hg1 : (0 : ℚ) < (g - 1 : ℕ) := by
    exact_mod_cast (show 0 < g - 1 by omega)
  rw [le_div_iff₀ hg1]
  have hcast : ((requests H - shortCount H q d g π hd r : ℚ)) = (Sc.card : ℚ) := by
    rw [← Nat.cast_sub hle_sub, hcard]
  rw [hcast]
  exact_mod_cast hsum

end BuyAtBulk.EdgeOnlyGap
