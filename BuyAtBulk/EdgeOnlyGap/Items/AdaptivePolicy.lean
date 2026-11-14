import BuyAtBulk.EdgeOnlyGap.Items.Exposure

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit adaptive query model, p. 2: decisions depend only on the revealed transcript. -/
structure AdaptivePolicy (H : FiniteGraph) (q T : ℕ) where
  next : List (Exposure H q) → Option (Edges H × Bool × Fin q)
  fresh : ∀ hist e reverse j, hist.length < T → next hist = some (e,reverse,j) →
    if reverse then j ∉ exposedTargets H q hist e else j ∉ exposedSources H q hist e

end BuyAtBulk.EdgeOnlyGap
