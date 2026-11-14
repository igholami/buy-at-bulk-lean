import BuyAtBulk.EdgeOnlyGap.Items.EdgeComponents

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

/-- Counting all components adds precisely the isolated vertices omitted by edgeComponents. -/
theorem componentCount (H : FiniteGraph) (W : Finset (Edges H)) :
    Nat.card (edgeSubgraph H W).ConnectedComponent =
      edgeComponents H W + (H.n - (edgeSupport H W).card) := by
  classical
  letI := Fintype.ofFinite (edgeSubgraph H W).ConnectedComponent
  let f := (edgeSubgraph H W).connectedComponentMk
  let S := edgeSupport H W
  have hisol : ∀ v, v ∉ S → ∀ u, (edgeSubgraph H W).Reachable v u → v = u := by
    intro v hv u hu
    obtain ⟨w⟩ := hu
    cases w with
    | nil => rfl
    | @cons v x u hadj rest =>
      exfalso
      apply hv
      rw [edgeSubgraph, SimpleGraph.fromRel_adj] at hadj
      change v ∈ edgeSupport H W
      rw [edgeSupport, Finset.mem_biUnion]
      rcases hadj.2 with ⟨e, he, rfl, rfl⟩ | ⟨e, he, rfl, rfl⟩
      · exact ⟨e, he, by simp⟩
      · exact ⟨e, he, by simp⟩
  have hall : Finset.univ.image f = Finset.univ := by
    ext c
    simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    exact Quot.mk_surjective c
  have hdis : Disjoint (S.image f) ((Finset.univ \ S).image f) := by
    rw [Finset.disjoint_left]
    intro c hc hd
    rcases Finset.mem_image.mp hc with ⟨u, hu, rfl⟩
    rcases Finset.mem_image.mp hd with ⟨v, hv, heq⟩
    have hv' := (Finset.mem_sdiff.mp hv).2
    have hvu := hisol v hv' u (SimpleGraph.ConnectedComponent.eq.mp heq)
    exact hv' (hvu.symm ▸ hu)
  have hinj : Set.InjOn f (↑(Finset.univ \ S : Finset (Fin H.n))) := by
    intro u hu v hv heq
    exact hisol u (Finset.mem_sdiff.mp hu).2 v (SimpleGraph.ConnectedComponent.eq.mp heq)
  have hsplit : S ∪ (Finset.univ \ S) = Finset.univ := by
    ext v
    simp
  have h := congrArg Finset.card (congrArg (Finset.image f) hsplit)
  rw [Finset.image_union, Finset.card_union_of_disjoint hdis,
    Finset.card_image_of_injOn hinj, hall, Finset.card_univ] at h
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_fin] at h
  simpa only [Nat.card_eq_fintype_card, edgeComponents, S, f] using h.symm

end BuyAtBulk.EdgeOnlyGap.ProofA
