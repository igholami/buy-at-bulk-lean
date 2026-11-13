import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofB

/-- Rank-nullity for binary chains indexed by a finite set. -/
theorem rankNullity {A B : Type} [Fintype A] [Fintype B]
    (f : (A → ZMod 2) →ₗ[ZMod 2] (B → ZMod 2)) :
    Module.finrank (ZMod 2) (LinearMap.ker f) +
      Module.finrank (ZMod 2) (LinearMap.range f) = Fintype.card A := by
  have h := LinearMap.finrank_range_add_finrank_ker f
  have hc : Module.finrank (ZMod 2) (A → ZMod 2) = Fintype.card A := Module.finrank_pi (ZMod 2)
  omega

end BuyAtBulk.EdgeOnlyGap.ProofB
