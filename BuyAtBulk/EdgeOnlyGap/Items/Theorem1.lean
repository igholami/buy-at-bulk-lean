import BuyAtBulk.EdgeOnlyGap.Items.GapFamily
import BuyAtBulk.EdgeOnlyGap.Items.InfiniteBases
import BuyAtBulk.EdgeOnlyGap.Items.Lemma1
import BuyAtBulk.EdgeOnlyGap.Items.PolynomialSupply
import BuyAtBulk.EdgeOnlyGap.Items.CombinedModification
import BuyAtBulk.EdgeOnlyGap.Items.ModifiedGap
import BuyAtBulk.EdgeOnlyGap.Items.LogScale

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Theorem 1 of the edge-only LP-gap note (p. 1, proved in §§5–6): an infinite family of edge-only instances with an Ω(log h / log log h) gap between the integral optimum and the attained real natural path LP, with strictly positive rational edge data and matching terminals. -/
theorem theorem1 : ∃ F : ℕ → BuyAtBulk.GraphData, GapFamily F := by
  classical
  obtain ⟨B, hB, hgrow⟩ := infiniteBases
  have hm0 : ∀ k, 0 < requests (B k) := by
    intro k
    have hh := proofC_requestsHandshake (B k) (k+4) (k+4) (hB k).1
    have : 0 < (B k).n * (k+4) := Nat.mul_pos (hB k).1.1 (by omega)
    omega
  have hT : ∀ k, k+4 ≤ threshold (B k) (k+4) := by
    intro k
    unfold threshold
    have := hm0 k
    nlinarith
  have hsparse : ∀ k, ∃ π : Lift (B k) (liftQ (B k).n (k+4) (k+4) (threshold (B k) (k+4))),
      LocallySparse (B k) (liftQ (B k).n (k+4) (k+4) (threshold (B k) (k+4))) (k+4)
        (threshold (B k) (k+4)) π := fun k =>
    lemma1 (B k) (k+4) (k+4) _ (by omega) (by omega)
      (fun v => le_of_eq ((hB k).1.2.1 v)) (hB k).1.2.2 (hT k)
  choose π hπ using hsparse
  have hq : ∀ k, 0 < liftQ (B k).n (k+4) (k+4) (threshold (B k) (k+4)) := by
    intro k
    unfold liftQ liftA
    have h1 := (hB k).1.1
    have h2 : 0 < threshold (B k) (k+4) := lt_of_lt_of_le (by omega) (hT k)
    positivity
  have hcm := fun k => combinedModification (B k) _ (k+4) (π k) (by omega) (hq k) (hB k).1
  refine ⟨fun k => privateLeaves (positiveData (B k) _ (k+4) (π k) (by omega))
    (1/(10*(requests (B k):ℚ))) (by positivity), ?_, ?_, ?_, ?_⟩
  · exact hgrow
  · intro k
    exact ⟨(hcm k).1, (hcm k).2.1, (hcm k).2.2.1⟩
  · obtain ⟨C, K, hC, hpoly⟩ := polynomialSupply
    refine ⟨C, K, 32, hC, fun k => ?_⟩
    have hp := hpoly (B k) (k+4) (by omega) (hB k).1
    dsimp only at hp
    refine ⟨?_, ?_, (hcm k).2.2.2.2.2.2⟩
    · rw [(hcm k).2.2.2.1]; exact hp.1
    · rw [(hcm k).2.2.2.2.1]; exact hp.2
  · obtain ⟨c, C, hc, -, g₀, hls⟩ := logScale
    refine ⟨c/24, by positivity, g₀, fun k hk => ?_⟩
    obtain ⟨opt, lp, hex, hlp, hgap⟩ :=
      modifiedGap (B k) _ (k+4) (π k) (by omega) (hq k) (hB k).1 (hπ k)
    obtain ⟨hreal, hrpos, hquot⟩ := exactOptimaRealPositive _ _ _ hex hlp
    obtain ⟨hll, -, -, hlow, -, -⟩ :=
      hls (B k) (k+4) (by omega) (by omega) (hB k).1 (hB k).2
    refine ⟨opt, lp, hex, hlp, hreal, hrpos, hll, ?_⟩
    rw [hquot]
    have hcast := (Rat.cast_le (K := ℝ)).mpr hgap
    push_cast at hcast ⊢
    have : c / 24 * Real.log (requests (B k)) / Real.log (Real.log (requests (B k))) =
        (c * Real.log (requests (B k)) / Real.log (Real.log (requests (B k)))) / 24 := by ring
    change c / 24 * Real.log (requests (B k)) / Real.log (Real.log (requests (B k))) ≤ _
    rw [this]
    push_cast at hlow
    linarith

end BuyAtBulk.EdgeOnlyGap
