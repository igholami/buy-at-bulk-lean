import BuyAtBulk.EdgeOnlyGap.Helpers.ProofAComponentSupport

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

private lemma walk_in_component_reachable (H : FiniteGraph) (W : Finset (Edges H))
    (c : (edgeSubgraph H W).ConnectedComponent) :
    ∀ {u v : Fin H.n} (w : (edgeSubgraph H W).Walk u v),
      (edgeSubgraph H W).connectedComponentMk u = c →
      (edgeSubgraph H (W.filter fun e => (edgeSubgraph H W).connectedComponentMk e.val.1 = c)).Reachable u v := by
  intro u v w
  induction w with
  | nil =>
    intro _
    exact SimpleGraph.Reachable.refl _
  | @cons u x v hadj rest ih =>
    intro hu
    have hx : (edgeSubgraph H W).connectedComponentMk x = c := by
      rw [← hu]
      exact (SimpleGraph.ConnectedComponent.eq.mpr hadj.reachable).symm
    have hadjU : (edgeSubgraph H (W.filter fun e => (edgeSubgraph H W).connectedComponentMk e.val.1 = c)).Adj u x := by
      unfold edgeSubgraph at hadj ⊢
      rw [SimpleGraph.fromRel_adj] at hadj ⊢
      rcases hadj with ⟨hne, ⟨e, heW, rfl, rfl⟩ | ⟨e, heW, rfl, rfl⟩⟩
      · refine ⟨hne, Or.inl ⟨e, ?_, rfl, rfl⟩⟩
        rw [Finset.mem_filter]
        exact ⟨heW, hu⟩
      · refine ⟨hne, Or.inr ⟨e, ?_, rfl, rfl⟩⟩
        rw [Finset.mem_filter]
        exact ⟨heW, hx⟩
    exact hadjU.reachable.trans (ih hx)

/-- The edge-containing part of a component is connected after restriction. -/
theorem componentConnected (H : FiniteGraph) (W : Finset (Edges H))
    (c : (edgeSubgraph H W).ConnectedComponent)
    (hU : (W.filter fun e => (edgeSubgraph H W).connectedComponentMk e.val.1 = c).Nonempty) :
    edgeComponents H (W.filter fun e => (edgeSubgraph H W).connectedComponentMk e.val.1 = c) = 1 := by
  let U := W.filter fun e => (edgeSubgraph H W).connectedComponentMk e.val.1 = c
  unfold edgeComponents
  obtain ⟨e₀, he₀⟩ := hU
  have he₀_supp : e₀.val.1 ∈ edgeSupport H U := by
    unfold edgeSupport
    rw [Finset.mem_biUnion]
    exact ⟨e₀, he₀, by simp⟩
  have h_all_eq : ∀ u ∈ edgeSupport H U,
      (edgeSubgraph H U).connectedComponentMk u = (edgeSubgraph H U).connectedComponentMk e₀.val.1 := by
    intro u hu
    have hu_c : (edgeSubgraph H W).connectedComponentMk u = c := by
      unfold edgeSupport at hu
      rw [Finset.mem_biUnion] at hu
      rcases hu with ⟨e, heU, hu_end⟩
      have he_c : (edgeSubgraph H W).connectedComponentMk e.val.1 = c :=
        (Finset.mem_filter.mp heU).2
      have heW : e ∈ W := (Finset.mem_filter.mp heU).1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu_end
      rcases hu_end with rfl | rfl
      · exact he_c
      · have hadj : (edgeSubgraph H W).Adj e.val.1 e.val.2 := by
          unfold edgeSubgraph
          rw [SimpleGraph.fromRel_adj]
          exact ⟨ne_of_lt e.prop.1, Or.inl ⟨e, heW, rfl, rfl⟩⟩
        rw [← he_c]
        exact (SimpleGraph.ConnectedComponent.eq.mpr hadj.reachable).symm
    have he₀_c : (edgeSubgraph H W).connectedComponentMk e₀.val.1 = c :=
      (Finset.mem_filter.mp he₀).2
    have hreachW : (edgeSubgraph H W).Reachable u e₀.val.1 :=
      SimpleGraph.ConnectedComponent.eq.mp (hu_c.trans he₀_c.symm)
    obtain ⟨w⟩ := hreachW
    exact SimpleGraph.ConnectedComponent.eq.mpr (walk_in_component_reachable H W c w hu_c)
  have himg : (edgeSupport H U).image (edgeSubgraph H U).connectedComponentMk =
      {(edgeSubgraph H U).connectedComponentMk e₀.val.1} := by
    ext x
    simp only [Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact h_all_eq u hu
    · rintro rfl
      exact ⟨e₀.val.1, he₀_supp, rfl⟩
  rw [himg, Finset.card_singleton]

end BuyAtBulk.EdgeOnlyGap.ProofA
