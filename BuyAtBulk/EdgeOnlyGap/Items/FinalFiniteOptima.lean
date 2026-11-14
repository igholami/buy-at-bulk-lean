import BuyAtBulk.EdgeOnlyGap.Items.CombinedModification
import BuyAtBulk.EdgeOnlyGap.Items.LocallySparse
import BuyAtBulk.EdgeOnlyGap.Items.PositiveLeafRestriction
import BuyAtBulk.EdgeOnlyGap.Items.IntegralLowerBound
import BuyAtBulk.EdgeOnlyGap.Items.LPPositive
import BuyAtBulk.EdgeOnlyGap.Items.IntegralAttainment
import BuyAtBulk.EdgeOnlyGap.Items.LPAttainment
import BuyAtBulk.EdgeOnlyGap.Items.ExactOptimaScalarBridge
import BuyAtBulk.EdgeOnlyGap.Items.ExactOptimaRealPositive

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit exact optimum/positivity bridge, p. 5, used in Theorem 1; includes the attained REAL minimum, its rational-value equality, positivity, and the actual real-denominator ratio. -/
theorem finalFiniteOptima (H : FiniteGraph) (q g : ℕ) (π : Lift H q)
    (hg : 4 ≤ g) (hq : 0 < q) (base : RegularBase H g g)
    (sparse : LocallySparse H q g (threshold H g) π) :
  let D := privateLeaves (positiveData H q g π (by omega))
    (1/(10*(requests H:ℚ))) (by positivity)
  ∃ opt lp : ℚ, ExactOptima D opt lp ∧
    0 < lp ∧ (H.n:ℚ) ≤ lp ∧ lp ≤ 2*H.n+17/5 ∧
    (H.n:ℚ)*g/4 ≤ opt ∧
    ((H.n:ℚ)*g/4)/(2*H.n+17/5) ≤ opt/lp ∧
    realLPValue D.toInstance = (lp : ℝ) ∧ 0 < realLPValue D.toInstance ∧
    ((H.n : ℝ)*g/4)/(2*H.n+17/5) ≤ (opt : ℝ) / realLPValue D.toInstance := by
  classical
  intro D
  have hg0 : 0 < g := by omega
  have hp : (0:ℚ) ≤ 1/(10*(requests H:ℚ)) := by positivity
  have hcm := combinedModification H q g π hg hq base
  have hEpos : EdgeOnlyInstance (positiveData H q g π hg0) :=
    (supplyValidity H q g π hg0 hq).1
  have hpw := positiveWitness H q g g π hg0 hq base
  have hplc := positiveLeavesCost _ hEpos _ hp
  obtain ⟨f0, hf0, hf0le⟩ := hcm.2.2.2.2.2.1
  obtain ⟨f, hf, hmin⟩ := lpAttainment D f0 hf0
  -- n ≤ LP through the leaf restriction and positive-modification transports
  have hlow : (H.n:ℚ) ≤ lpObjective D.toInstance f := by
    obtain ⟨g1, hg1, hle1⟩ := positiveLeafRestriction _ hEpos _ hp f hf
    obtain ⟨g2, hg2, hle2⟩ := hpw.2.2.2 g1 hg1
    have := (lpPositive H q g g π hg0 base g2 hg2).1
    linarith
  have hnpos : (0:ℚ) < H.n := by exact_mod_cast base.1
  have hlppos : 0 < lpObjective D.toInstance f := by linarith
  -- integral routing seed from LP feasibility
  have hpath : ∀ i, ∃ p, D.toInstance.allowed i p = true := by
    intro i
    by_contra hno
    push_neg at hno
    have hzero : ∑ p, f.flow i p = 0 :=
      Finset.sum_eq_zero fun p _ => hf.2.2.1 i p (by simpa using hno p)
    have := hf.2.2.2.1 i
    rw [hzero] at this
    exact zero_ne_one this
  let seed : D.toInstance.IntegralRouting :=
    ⟨fun i => (hpath i).choose, fun i => (hpath i).choose_spec⟩
  obtain ⟨r, hr⟩ := integralAttainment D seed
  have hopt : (H.n:ℚ)*g/4 ≤ integralObjective D.toInstance r := by
    obtain ⟨s1, hs1⟩ := hplc.2.2.2 r
    obtain ⟨s2, hs2⟩ := hpw.2.2.1 s1
    have hlb := integralLowerBound H q g g π hg hg base sparse s2
    have hmin' : min ((g:ℚ)/2) ((g:ℚ)/4) = (g:ℚ)/4 := by
      apply min_eq_right
      have : (0:ℚ) ≤ g := by positivity
      linarith
    rw [hmin'] at hlb
    have : (H.n:ℚ)*g/4 = (H.n:ℚ)*((g:ℚ)/4) := by ring
    linarith
  have hex : ExactOptima D (integralObjective D.toInstance r) (lpObjective D.toInstance f) := by
    rw [← exactOptimaScalarBridge]
    exact ⟨⟨r, rfl⟩, hr, ⟨f, hf, rfl⟩, fun g hg => hmin g hg⟩
  have hup : lpObjective D.toInstance f ≤ 2*H.n+17/5 := (hmin f0 hf0).trans hf0le
  have hratio : ((H.n:ℚ)*g/4)/(2*H.n+17/5) ≤
      integralObjective D.toInstance r / lpObjective D.toInstance f := by
    have h0 : (0:ℚ) ≤ (H.n:ℚ)*g/4 := by positivity
    exact div_le_div₀ (h0.trans hopt) hopt hlppos hup
  obtain ⟨hreal, hrpos, hquot⟩ := exactOptimaRealPositive D _ _ hex hlppos
  refine ⟨integralObjective D.toInstance r, lpObjective D.toInstance f, hex, hlppos, hlow,
    hup, hopt, hratio, hreal, hrpos, ?_⟩
  rw [hquot]
  have := (Rat.cast_le (K := ℝ)).mpr hratio
  push_cast at this ⊢
  exact this

end BuyAtBulk.EdgeOnlyGap
