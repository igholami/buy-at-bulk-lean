import BuyAtBulk.EdgeOnlyGap.Items.Optima

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit bridge, p. 1, used in Theorem 1: finite nonempty routing space. -/
theorem integralAttainment (D : BuyAtBulk.GraphData)
    (seed : D.toInstance.IntegralRouting) :
  ∃ r : D.toInstance.IntegralRouting,
    ∀ s : D.toInstance.IntegralRouting,
      integralObjective D.toInstance r ≤ integralObjective D.toInstance s := by
  classical
  letI : Nonempty D.toInstance.IntegralRouting := ⟨seed⟩
  let encode : D.toInstance.IntegralRouting →
      (Fin D.toInstance.requestCount → Fin D.toInstance.pathCount) := fun r => r.path
  have hinj : Function.Injective encode := by
    intro a b h
    cases a
    cases b
    cases h
    rfl
  letI : Finite D.toInstance.IntegralRouting := Finite.of_injective encode hinj
  letI := Fintype.ofFinite D.toInstance.IntegralRouting
  obtain ⟨r, _, hr⟩ := Finset.exists_min_image Finset.univ
    (integralObjective D.toInstance) ⟨seed, Finset.mem_univ _⟩
  exact ⟨r, fun s => hr s (Finset.mem_univ _)⟩

end BuyAtBulk.EdgeOnlyGap
