import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBWitnessWeighted
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBPathResourceCard
import BuyAtBulk.EdgeOnlyGap.Items.SupplyValidity
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofB

/-- Every displayed witness path traverses three edges, so its average resource count is three. -/
theorem witnessMass (H : FiniteGraph) (q d : ℕ) (π : Lift H q) (hd : 0 < d)
    (hq : 0 < q) (i : Fin (supplyData H q d π hd).requestCount) :
    (∑ p, (((supplyData H q d π hd).toInstance.uses p).card : ℚ) *
      (fractionalWitness H q d π hd).flow i p) = 3 := by
  classical
  rw [witnessWeighted]
  have hc (j : Fin q) :
      ((supplyData H q d π hd).toInstance.uses ((supplyData H q d π hd).encode i
        (witnessPath H q π ((Fintype.equivFin (Edges H)).symm i) j))).card = 3 := by
    erw [BuyAtBulk.GraphData.uses_encode]
    exact (pathResourceCard _ (supplyValidity H q d π hd hq).1 i
      (witnessPath H q π ((Fintype.equivFin (Edges H)).symm i) j)).trans rfl
  simp_rw [hc]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hqne : (q : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  field_simp [hqne]
  norm_num

end BuyAtBulk.EdgeOnlyGap.ProofB
