import BuyAtBulk.EdgeOnlyGap.Items.NaturalEncode
import BuyAtBulk.EdgeOnlyGap.Items.NaturalRealEncode
import BuyAtBulk.EdgeOnlyGap.Items.NaturalDecode
import BuyAtBulk.EdgeOnlyGap.Items.NaturalRealDecode

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit scalar-domain correspondence for equation (2), p. 1, used in Theorem 1: no coordinates omitted on either scalar domain: both encode/decode pairs are inverse. -/
theorem naturalCoordinateRoundtrip (I : BuyAtBulk.Instance) :
    (∀ f : I.FractionalSolution, naturalDecode I (naturalEncode I f) = f) ∧
    (∀ z, naturalEncode I (naturalDecode I z) = z) ∧
    (∀ f : RealFractionalSolution I, naturalRealDecode I (naturalRealEncode I f) = f) ∧
    (∀ z, naturalRealEncode I (naturalRealDecode I z) = z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f
    cases f
    simp [naturalDecode, naturalEncode]
  · intro z
    funext j
    obtain ⟨a, rfl⟩ := (naturalCoordinateEquiv I).surjective j
    cases a <;> simp [naturalEncode, naturalDecode]
  · intro f
    rcases f with ⟨a, b⟩
    simp [naturalRealDecode, naturalRealEncode]
  · intro z
    funext j
    obtain ⟨a, rfl⟩ := (naturalCoordinateEquiv I).surjective j
    cases a <;> simp [naturalRealEncode, naturalRealDecode]

end BuyAtBulk.EdgeOnlyGap
