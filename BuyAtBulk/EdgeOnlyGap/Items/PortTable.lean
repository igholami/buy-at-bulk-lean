import BuyAtBulk.EdgeOnlyGap.Items.Lift

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit port convention, p. 2: at most d incident ports, with no repeated base edge. -/
structure PortTable (H : FiniteGraph) (d : ℕ) where
  port : Fin H.n → Fin d → Option (Edges H)
  incident : ∀ v p e, port v p = some e → v=e.val.1 ∨ v=e.val.2
  injective : ∀ v p p' e, port v p = some e → port v p' = some e → p=p'
  complete : ∀ v e, v=e.val.1 ∨ v=e.val.2 → ∃ p, port v p = some e

end BuyAtBulk.EdgeOnlyGap
