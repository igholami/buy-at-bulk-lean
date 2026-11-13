import BuyAtBulk.EdgeOnlyGap.Items.ProjectedCycle
import BuyAtBulk.EdgeOnlyGap.Items.LiftAsFiniteGraph
import BuyAtBulk.EdgeOnlyGap.Items.GirthAtLeast

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 2: lift girth preservation, including acyclic bases. -/
theorem liftGirth (H : FiniteGraph) (q g : ℕ) (π : Lift H q)
    (girth : GirthAtLeast H g) : GirthAtLeast (lifted H q π) g := by
  unfold GirthAtLeast at girth ⊢
  rw [SimpleGraph.le_egirth] at girth ⊢
  intro a w hw
  let ev : Fin (lifted H q π).n ≃ Fin H.n × Fin q :=
    (finCongr (by simp [lifted] : (lifted H q π).n = Fintype.card (Fin H.n × Fin q))).trans
      (Fintype.equivFin (Fin H.n × Fin q)).symm
  let hom : (lifted H q π).graph →g liftGraph H q π :=
    { toFun := ev
      map_rel' := fun h => h }
  have hinj : Function.Injective hom := ev.injective
  have hcycle : (w.map hom).IsCycle := hw.map hinj
  obtain ⟨u, c, hc, hlen⟩ := (projectedCycle H q π (hom a) (w.map hom) hcycle).2
  rw [SimpleGraph.Walk.length_map] at hlen
  exact le_trans (girth u c hc) (by exact_mod_cast hlen)

end BuyAtBulk.EdgeOnlyGap
