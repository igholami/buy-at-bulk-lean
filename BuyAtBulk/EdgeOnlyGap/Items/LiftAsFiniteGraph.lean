import BuyAtBulk.EdgeOnlyGap.Items.Lift

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit coordinate transport, p. 2. -/
def lifted (H : FiniteGraph) (q : ℕ) (π : Lift H q) : FiniteGraph where
  n := H.n * q
  graph := (liftGraph H q π).comap
    ((Fintype.equivFin (Fin H.n × Fin q)).symm ∘
      (finCongr (by simp : H.n * q = Fintype.card (Fin H.n × Fin q))))

end BuyAtBulk.EdgeOnlyGap
