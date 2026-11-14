import BuyAtBulk.EdgeOnlyGap.Items.PositiveModification
import BuyAtBulk.EdgeOnlyGap.Items.PrivateLeaves
import BuyAtBulk.EdgeOnlyGap.Items.CoefficientBits
import BuyAtBulk.EdgeOnlyGap.Items.RegularBase
import BuyAtBulk.EdgeOnlyGap.Items.FinalCoefficientData
import BuyAtBulk.EdgeOnlyGap.Items.PositiveWitness
import BuyAtBulk.EdgeOnlyGap.Items.PositiveLeavesCost
import BuyAtBulk.EdgeOnlyGap.Items.SupplyValidity
import BuyAtBulk.EdgeOnlyGap.Items.SupplySizes
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBLeafEdgeOnly
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBLeafMatching

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 5: both modifications, explicit size, positivity and 2n+17/5 witness. -/
theorem combinedModification (H : FiniteGraph) (q g : ℕ) (π : Lift H q)
    (hg : 4 ≤ g) (hq : 0 < q) (base : RegularBase H g g) :
  let D := privateLeaves (positiveData H q g π (by omega))
    (1/(10*(requests H:ℚ))) (by positivity)
  EdgeOnlyInstance D ∧ MatchingTerminals D ∧
  (∀ a, 0 < D.buying a ∧ 0 < D.length a) ∧
  Fintype.card D.Vertex = H.n*(q+1)+2*requests H ∧
  D.resourceCount = q*(H.n+requests H)+2*requests H ∧
  (∃ f : D.toInstance.FractionalSolution, D.toInstance.Feasible f ∧
    lpObjective D.toInstance f ≤ 2*H.n+17/5) ∧
  CoefficientsBounded D 32 := by
  intro D
  have hg0 : 0 < g := by omega
  have hm := proofC_requestsHandshake H g g base
  have hm0 : 0 < requests H := by
    have := base.1
    have : 0 < H.n * g := Nat.mul_pos this hg0
    omega
  have hmq : (0:ℚ) < requests H := by exact_mod_cast hm0
  have hEpos : EdgeOnlyInstance (positiveData H q g π hg0) :=
    (supplyValidity H q g π hg0 hq).1
  have hpw := positiveWitness H q g g π hg0 hq base
  have hp : (0:ℚ) ≤ 1/(10*(requests H:ℚ)) := by positivity
  have hsz := supplySizes H q g π hg0
  refine ⟨ProofB.leafEdgeOnly _ hEpos _ hp, ProofB.leafMatching _ _ hp, ?_, ?_, ?_, ?_,
    (finalCoefficientData H q g π hg base).2⟩
  · intro a
    simp only [D, privateLeaves]
    split
    · rename_i j _
      exact hpw.1 j
    · exact ⟨by positivity, by positivity⟩
  · simp only [D, privateLeaves, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool]
    rw [show Fintype.card (positiveData H q g π hg0).Vertex = H.n*(q+1) from hsz.1]
    rw [show (positiveData H q g π hg0).requestCount = requests H from rfl]
    ring
  · simp only [D, privateLeaves, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool]
    rw [show (positiveData H q g π hg0).resourceCount = q*(H.n+requests H) from hsz.2]
    rw [show (positiveData H q g π hg0).requestCount = requests H from rfl]
    ring
  · obtain ⟨f, hf, hb, hr⟩ := hpw.2.1
    obtain ⟨f', hf', heq⟩ := (positiveLeavesCost _ hEpos _ hp).2.2.1 f hf
    refine ⟨f', hf', ?_⟩
    rw [heq]
    unfold lpObjective
    rw [hb, hr]
    have hrc : ((positiveData H q g π hg0).requestCount : ℚ) = requests H := rfl
    rw [hrc]
    field_simp
    ring_nf
    norm_num

end BuyAtBulk.EdgeOnlyGap
