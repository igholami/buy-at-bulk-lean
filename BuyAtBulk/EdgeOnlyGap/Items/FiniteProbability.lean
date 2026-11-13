import Mathlib.Data.Real.Basic
import BuyAtBulk.EdgeOnlyGap.Items.LiftAsFiniteGraph

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 2: finite uniform product space of permutations. -/
def finiteProbability {Ω : Type} [Fintype Ω] (E : Ω → Prop) : ℝ :=
  (Fintype.card {ω // E ω} : ℝ) / Fintype.card Ω

end BuyAtBulk.EdgeOnlyGap
