import BuyAtBulk.EdgeOnlyGap.Items.LocallySparse

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Lemma 1 implicit empty-base case, p. 2. Q=0 is retained exactly. -/
theorem emptyLift (H : FiniteGraph) (d g T : ℕ) (empty : H.n = 0) :
  ∃ π : Lift H (liftQ H.n d g T),
    LocallySparse H (liftQ H.n d g T) g T π := by
  refine ⟨fun _ => Equiv.refl _, ?_⟩
  intro W _
  have hW : W = ∅ := by
    ext e
    simp only [Finset.notMem_empty, iff_false]
    intro _
    have hn : (lifted H (liftQ H.n d g T) (fun _ => Equiv.refl _)).n = 0 := by
      simp [lifted, empty]
    exact Fin.elim0 (Fin.cast hn e.val.1)
  subst hW
  simp [beta, edgeSupport, edgeComponents]

end BuyAtBulk.EdgeOnlyGap
