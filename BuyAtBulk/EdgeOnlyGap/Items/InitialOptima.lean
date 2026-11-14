import BuyAtBulk.EdgeOnlyGap.Items.LPPositive
import BuyAtBulk.EdgeOnlyGap.Items.IntegralLowerBound
import BuyAtBulk.EdgeOnlyGap.Items.Lemma2
import BuyAtBulk.EdgeOnlyGap.Items.ExactOptimaScalarBridge
import BuyAtBulk.EdgeOnlyGap.Items.IntegralAttainment
import BuyAtBulk.Model.LPOptimum

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Lemma 2 “in particular LP ≤ 2n”, p. 3; equation (10), p. 4;
implicit attainment and positivity bridge for general d,g, used in §5. -/
theorem initialOptima (H : FiniteGraph) (q d g : ℕ) (π : Lift H q)
    (hd : 4 ≤ d) (hg : 4 ≤ g) (hq : 0 < q) (base : RegularBase H d g)
    (sparse : LocallySparse H q g (threshold H g) π) :
  ∃ opt lp : ℚ, ExactOptima (supplyData H q d π (by omega)) opt lp ∧
    0 < lp ∧ (H.n:ℚ) ≤ lp ∧ lp ≤ 2*H.n ∧
    (H.n:ℚ) * min ((d:ℚ)/2) ((g:ℚ)/4) ≤ opt := by
  classical
  have hd0 : 0 < d := by omega
  obtain ⟨hwf, hwb, hwr, -⟩ := lemma2 H d g q base hd hg hd0 hq π
  obtain ⟨f, hf, hmin⟩ := BuyAtBulk.NodeReduction.exists_optimal_canonical
    (supplyData H q d π hd0) _ hwf
  -- an allowed path for every request, from LP feasibility
  have hpath : ∀ i, ∃ p, (supplyData H q d π hd0).toInstance.allowed i p = true := by
    intro i
    by_contra hno
    push_neg at hno
    have hzero : ∑ p, f.flow i p = 0 :=
      Finset.sum_eq_zero fun p _ => hf.2.2.1 i p (by simpa using hno p)
    have := hf.2.2.2.1 i
    rw [hzero] at this
    exact zero_ne_one this
  let seed : (supplyData H q d π hd0).toInstance.IntegralRouting :=
    ⟨fun i => (hpath i).choose, fun i => (hpath i).choose_spec⟩
  obtain ⟨r, hr⟩ := integralAttainment (supplyData H q d π hd0) seed
  have hpos := lpPositive H q d g π hd0 base f hf
  refine ⟨integralObjective (supplyData H q d π hd0).toInstance r,
    lpObjective (supplyData H q d π hd0).toInstance f, ?_, hpos.2, hpos.1, ?_, ?_⟩
  · rw [← exactOptimaScalarBridge]
    exact ⟨⟨r, rfl⟩, hr, ⟨f, hf, rfl⟩, fun g hg => hmin g hg⟩
  · have := hmin _ hwf
    unfold lpObjective
    rw [hwb, hwr] at this
    linarith
  · exact integralLowerBound H q d g π hd hg base sparse r

end BuyAtBulk.EdgeOnlyGap
