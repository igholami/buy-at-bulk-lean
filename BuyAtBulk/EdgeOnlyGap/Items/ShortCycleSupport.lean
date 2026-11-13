import BuyAtBulk.EdgeOnlyGap.Items.ProjectionBoundary
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBProjectionSupport

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 4: projected short chain plus its demand edge is a cycle supported on ≤g−1 edges. -/
theorem shortCycleSupport (H : FiniteGraph) (q d g : ℕ) (π : Lift H q) (hd : 0 < d)
    (hg : 4 ≤ g) (r : (supplyData H q d π hd).toInstance.IntegralRouting)
    (i : Fin (requests H)) (short : coreTraversals H q d π hd r i < g-1) :
  let e := (Fintype.equivFin (Edges H)).symm i
  let y := chainProjection H q d π hd r (routeChain H q d π hd r i)
  let z := y + Pi.single e (1 : ZMod 2)
  (∀ v, baseBoundary H z v = 0) ∧ (Finset.univ.filter fun a => z a ≠ 0).card ≤ g-1  := by
  classical
  intro e y z
  have hadd : ∀ v, baseBoundary H z v =
      baseBoundary H y v + baseBoundary H (Pi.single e (1 : ZMod 2)) v := by
    intro v
    unfold baseBoundary
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    dsimp [z]
    split_ifs <;> simp
  have hsingle : ∀ v, baseBoundary H (Pi.single e (1 : ZMod 2)) v =
      if v = e.val.1 ∨ v = e.val.2 then 1 else 0 := by
    intro v
    unfold baseBoundary
    rw [Finset.sum_eq_single e]
    · simp
    · intro b _ hbe
      simp [Pi.single_apply, hbe]
    · simp
  refine ⟨?_, ?_⟩
  · intro v
    rw [hadd, hsingle, (projectionBoundary H q d π hd r).2 i |>.2 v]
    have hne : e.val.1 ≠ e.val.2 := ne_of_lt e.property.1
    by_cases h₁ : v = e.val.1 <;> by_cases h₂ : v = e.val.2 <;>
      simp_all [e] <;> decide
  · let Y := Finset.univ.filter fun a => y a ≠ 0
    have hsub : (Finset.univ.filter fun a => z a ≠ 0) ⊆ Y ∪ {e} := by
      intro a ha
      by_cases h : a = e
      · simp [h]
      · have hya : y a ≠ 0 := by
          simpa [z, Pi.single_apply, h] using (Finset.mem_filter.mp ha).2
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hya⟩)
    have hproj : Y.card ≤ coreTraversals H q d π hd r i :=
      ProofB.projectionSupport H q d π hd r i
    calc
      (Finset.univ.filter fun a => z a ≠ 0).card ≤ (Y ∪ {e}).card := Finset.card_le_card hsub
      _ ≤ Y.card + 1 := by simpa using Finset.card_union_le Y {e}
      _ ≤ g - 1 := by omega

end BuyAtBulk.EdgeOnlyGap
