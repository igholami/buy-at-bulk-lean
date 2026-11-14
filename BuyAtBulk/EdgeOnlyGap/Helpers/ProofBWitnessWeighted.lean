import BuyAtBulk.EdgeOnlyGap.Items.FractionalWitness
import Mathlib.Algebra.BigOperators.Ring.Finset

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofB

/-- Weighted sums of the canonical split witness reduce to its q displayed paths. -/
theorem witnessWeighted (H : FiniteGraph) (q d : ℕ) (π : Lift H q) (hd : 0 < d)
    (i : Fin (supplyData H q d π hd).requestCount)
    (w : Fin (supplyData H q d π hd).toInstance.pathCount → ℚ) :
    (∑ p, w p * (fractionalWitness H q d π hd).flow i p) =
      ∑ j : Fin q, w ((supplyData H q d π hd).encode i
        (witnessPath H q π ((Fintype.equivFin (Edges H)).symm i) j)) * (1 / (q : ℚ)) := by
  classical
  change (∑ p, w p * (∑ j : Fin q, if p = (supplyData H q d π hd).encode i
    (witnessPath H q π ((Fintype.equivFin (Edges H)).symm i) j) then 1 / (q : ℚ) else 0)) = _
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp

end BuyAtBulk.EdgeOnlyGap.ProofB
