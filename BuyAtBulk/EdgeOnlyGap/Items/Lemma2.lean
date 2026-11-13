import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBFractionalWitness
import BuyAtBulk.EdgeOnlyGap.Items.FractionalWitness
import BuyAtBulk.EdgeOnlyGap.Items.RegularBase
import BuyAtBulk.EdgeOnlyGap.Items.Handshaking
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Lemma 2 and p. 3: feasible LP point B=R=n, with per-commodity edge loads. -/
theorem lemma2 (H : FiniteGraph) (d g q : ℕ) (base : RegularBase H d g)
    (hd4 : 4 ≤ d) (hg4 : 4 ≤ g) (hd : 0 < d) (hq : 0 < q) (π : Lift H q) :
  let D := supplyData H q d π hd
  let f := fractionalWitness H q d π hd
  D.toInstance.Feasible f ∧ D.toInstance.buyingCost f = H.n ∧
    D.toInstance.rentalCost f = H.n ∧
    (∀ i a, D.toInstance.resourceFlow f i a ≤ 1 / (q : ℚ)) := by
  exact ProofB.fractionalWitnessCosts H d g q base hd hq π

end BuyAtBulk.EdgeOnlyGap
