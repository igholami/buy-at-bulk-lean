import BuyAtBulk.EdgeOnlyGap.Items.PrivateLeaves
import BuyAtBulk.EdgeOnlyGap.Items.Optima
import BuyAtBulk.EdgeOnlyGap.Items.PositiveLeavesCost
import BuyAtBulk.EdgeOnlyGap.Items.PositiveLeafRestriction
import BuyAtBulk.EdgeOnlyGap.Items.ExactOptimaScalarBridge
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBLeafIntegralExtension

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 5: zero pendants preserve both optima and force a terminal matching. -/
theorem zeroLeavesOptima (D : BuyAtBulk.GraphData) (edge : EdgeOnlyInstance D) :
  MatchingTerminals (privateLeaves D 0 (by norm_num)) ∧
  EdgeOnlyInstance (privateLeaves D 0 (by norm_num)) ∧
  (∀ opt lp : ℚ, ExactOptima (privateLeaves D 0 (by norm_num)) opt lp ↔
    ExactOptima D opt lp) := by
  classical
  let hp : (0 : ℚ) ≤ 0 := le_rfl
  let E := privateLeaves D 0 hp
  obtain ⟨hm,he,hfrac,hint⟩ := positiveLeavesCost D edge 0 hp
  refine ⟨hm,he,?_⟩
  intro opt lp
  have extF : ∀ f : D.toInstance.FractionalSolution, D.toInstance.Feasible f →
      ∃ g : E.toInstance.FractionalSolution, E.toInstance.Feasible g ∧
        lpObjective E.toInstance g = lpObjective D.toInstance f := by
    intro f hf
    obtain ⟨g,hg,hcost⟩ := hfrac f hf
    exact ⟨g,hg,by simpa only [mul_zero,add_zero] using hcost⟩
  have extI := ProofB.leafIntegralExtension D edge
  have equivRat : RationalExactOptima E opt lp ↔ RationalExactOptima D opt lp := by
    constructor
    · rintro ⟨⟨r,hr⟩,hminI,⟨f,hf,hfc⟩,hminF⟩
      have minI : ∀ s : D.toInstance.IntegralRouting, opt ≤ integralObjective D.toInstance s := by
        intro s
        obtain ⟨t,ht⟩ := extI s
        exact ht ▸ hminI t
      have minF : ∀ g : D.toInstance.FractionalSolution, D.toInstance.Feasible g →
          lp ≤ lpObjective D.toInstance g := by
        intro g hg
        obtain ⟨k,hk,hc⟩ := extF g hg
        exact hc ▸ hminF k hk
      obtain ⟨s,hs⟩ := hint r
      obtain ⟨g,hg,hgc⟩ := positiveLeafRestriction D edge 0 hp f hf
      refine ⟨⟨s,le_antisymm (hs.trans (le_of_eq hr)) (minI s)⟩,minI,
        ⟨g,hg,le_antisymm (hgc.trans (le_of_eq hfc)) (minF g hg)⟩,minF⟩
    · rintro ⟨⟨r,hr⟩,hminI,⟨f,hf,hfc⟩,hminF⟩
      obtain ⟨s,hs⟩ := extI r
      obtain ⟨g,hg,hgc⟩ := extF f hf
      refine ⟨⟨s,hs.trans hr⟩,?_,⟨g,hg,hgc.trans hfc⟩,?_⟩
      · intro t
        obtain ⟨u,hu⟩ := hint t
        exact (hminI u).trans hu
      · intro k hk
        obtain ⟨u,hu,huc⟩ := positiveLeafRestriction D edge 0 hp k hk
        exact (hminF u hu).trans huc
  exact (exactOptimaScalarBridge E opt lp).symm.trans
    (equivRat.trans (exactOptimaScalarBridge D opt lp))

end BuyAtBulk.EdgeOnlyGap
