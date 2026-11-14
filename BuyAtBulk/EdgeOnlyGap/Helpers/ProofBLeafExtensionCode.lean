import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBLeafExtensionUses
import BuyAtBulk.Model.NodeReduction.Transport
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.EdgeOnlyGap.ProofB
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def leafExtensionCode (D : BuyAtBulk.GraphData) (p : ℚ) (hp : 0 ≤ p)
    (q : Fin D.toInstance.pathCount) : Fin (privateLeaves D p hp).toInstance.pathCount :=
  let t := D.decode q
  (privateLeaves D p hp).encode t.1 (leafPathExtension D p hp t.1 t.2)

theorem leafExtensionLegal (D : BuyAtBulk.GraphData) (p : ℚ) (hp : 0 ≤ p)
    (i : Fin D.requestCount) (q : Fin D.toInstance.pathCount) :
    (privateLeaves D p hp).toInstance.allowed i (leafExtensionCode D p hp q) =
      D.toInstance.allowed i q := by
  have hd : (privateLeaves D p hp).decode (leafExtensionCode D p hp q) =
    ⟨(D.decode q).1,leafPathExtension D p hp (D.decode q).1 (D.decode q).2⟩ :=
    (privateLeaves D p hp).decode_encode _ _
  change decide (((privateLeaves D p hp).decode (leafExtensionCode D p hp q)).1 = i) = _
  rw [hd]

theorem leafExtensionCodeOldUses (D : BuyAtBulk.GraphData) (edge : EdgeOnlyInstance D)
    (p : ℚ) (hp : 0 ≤ p) (q : Fin D.toInstance.pathCount) (a : Fin D.resourceCount) :
    leafOldResource D p hp a ∈ (privateLeaves D p hp).toInstance.uses (leafExtensionCode D p hp q) ↔
      a ∈ D.toInstance.uses q := by
  have hd : (privateLeaves D p hp).decode (leafExtensionCode D p hp q) =
    ⟨(D.decode q).1,leafPathExtension D p hp (D.decode q).1 (D.decode q).2⟩ :=
    (privateLeaves D p hp).decode_encode _ _
  change _ ∈ (privateLeaves D p hp).pathResources _ ↔ _
  rw [hd]
  exact leafExtensionOldUses D edge p hp _ _ a

theorem leafExtensionCodePendantUses (D : BuyAtBulk.GraphData)
    (p : ℚ) (hp : 0 ≤ p) (q : Fin D.toInstance.pathCount) (j : Fin D.requestCount) (b : Bool) :
    leafPendantResource D p hp j b ∈ (privateLeaves D p hp).toInstance.uses (leafExtensionCode D p hp q) ↔
      j = (D.decode q).1 := by
  have hd : (privateLeaves D p hp).decode (leafExtensionCode D p hp q) =
    ⟨(D.decode q).1,leafPathExtension D p hp (D.decode q).1 (D.decode q).2⟩ :=
    (privateLeaves D p hp).decode_encode _ _
  change _ ∈ (privateLeaves D p hp).pathResources _ ↔ _
  rw [hd]
  exact leafExtensionPendantUses D p hp _ _ j b

/-- Reindex all leaf resources into original resources and private pendants. -/
theorem leafResourceSum (D : BuyAtBulk.GraphData) (p : ℚ) (hp : 0 ≤ p)
    (F : Fin (privateLeaves D p hp).resourceCount → ℚ) :
    (∑ a, F a) = (∑ a, F (leafOldResource D p hp a)) +
      ∑ j, ∑ b, F (leafPendantResource D p hp j b) := by
  have h := (Equiv.sum_comp (Fintype.equivFin
    (Fin D.resourceCount ⊕ (Fin D.requestCount × Bool))) F).symm
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type] at h
  convert h using 1
  · apply Finset.sum_congr (by ext; simp)
    intro a _; rfl
  · apply congrArg₂ (· + ·)
    · apply Finset.sum_congr (by ext; simp)
      intro a _; rfl
    · apply Finset.sum_congr (by ext; simp)
      intro j _
      apply Finset.sum_congr (by ext; simp)
      intro b _; rfl
end BuyAtBulk.EdgeOnlyGap.ProofB
