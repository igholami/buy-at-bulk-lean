import BuyAtBulk.EdgeOnlyGap.Items.PrivateLeaves

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofB

/-- Private terminal leaves are distinct even when original terminals coincide. -/
theorem leafMatching (D : BuyAtBulk.GraphData) (p : ℚ) (hp : 0 ≤ p) :
    MatchingTerminals (privateLeaves D p hp) := by
  classical
  intro ⟨i, b⟩ ⟨j, c⟩ h
  cases b <;> cases c <;>
    simp_all [privateLeaves]

end BuyAtBulk.EdgeOnlyGap.ProofB
