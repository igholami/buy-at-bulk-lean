import BuyAtBulk.EdgeOnlyGap.Items.EdgeOnlyInstance

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofB

/-- Full edge resources count every edge of a simple path exactly once,
including the nil path when its endpoints coincide. -/
theorem pathResourceCard (D : BuyAtBulk.GraphData) (edge : EdgeOnlyInstance D)
    (i : Fin D.requestCount) (P : D.graph.Path (D.source i) (D.target i)) :
    (D.pathResources ⟨i, P⟩).card = P.val.length := by
  classical
  choose e he using edge.2.1
  have hm (a : Fin D.resourceCount) : a ∈ D.pathResources ⟨i, P⟩ ↔ e a ∈ P.val.edges := by
    simp only [BuyAtBulk.GraphData.pathResources, Finset.mem_filter, Finset.mem_univ,
      true_and, he]
  have hc : (D.pathResources ⟨i, P⟩).card = P.val.edges.toFinset.card := by
    apply Finset.card_bij (fun a _ => e a)
    · intro a ha
      exact List.mem_toFinset.mpr ((hm a).mp ha)
    · intro a ha b hb hab
      apply D.location_injective
      rw [he a, he b, hab]
    · intro t ht
      have ht' := List.mem_toFinset.mp ht
      obtain ⟨a, ha⟩ := edge.2.2 t (P.val.edges_subset_edgeSet ht')
      have hea : e a = t := Sum.inr.inj ((he a).symm.trans ha)
      exact ⟨a, (hm a).mpr (hea.symm ▸ ht'), hea⟩
  rw [hc, List.toFinset_card_of_nodup P.property.isTrail.edges_nodup,
    SimpleGraph.Walk.length_edges]

end BuyAtBulk.EdgeOnlyGap.ProofB
