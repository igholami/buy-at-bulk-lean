import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBPathBoundary
import BuyAtBulk.EdgeOnlyGap.Items.EdgeOnlyInstance

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap.ProofB
attribute [local instance] Classical.propDecidable

/-- Transfer the simple-path boundary to the canonical full edge resources. -/
theorem resourcePathBoundary (D : BuyAtBulk.GraphData) [DecidableEq D.Vertex] (edge : EdgeOnlyInstance D)
    (i : Fin D.requestCount) (P : D.graph.Path (D.source i) (D.target i))
    (v : D.Vertex) :
    (∑ a ∈ D.pathResources ⟨i, P⟩,
      if ∃ e, D.location a = Sum.inr e ∧ v ∈ e then (1 : ZMod 2) else 0) =
      (if v = D.source i then 1 else 0) + (if v = D.target i then 1 else 0) := by
  classical
  choose e he using edge.2.1
  have hm (a : Fin D.resourceCount) : a ∈ D.pathResources ⟨i, P⟩ ↔ e a ∈ P.val.edges := by
    simp only [BuyAtBulk.GraphData.pathResources, Finset.mem_filter, Finset.mem_univ,
      true_and, he]
  calc
    _ = ∑ t ∈ P.val.edges.toFinset, if v ∈ t then (1 : ZMod 2) else 0 := by
      apply Finset.sum_bij (fun a _ => e a)
      · intro a ha
        exact List.mem_toFinset.mpr ((hm a).mp ha)
      · intro a ha b hb hab
        apply D.location_injective
        rw [he a, he b, hab]
      · intro t ht
        obtain ⟨a, ha⟩ := edge.2.2 t (P.val.edges_subset_edgeSet (List.mem_toFinset.mp ht))
        have hea : e a = t := Sum.inr.inj ((he a).symm.trans ha)
        exact ⟨a, (hm a).mpr (hea.symm ▸ List.mem_toFinset.mp ht), hea⟩
      · intro a ha
        simp [he]
    _ = _ := pathBoundary P v

end BuyAtBulk.EdgeOnlyGap.ProofB
