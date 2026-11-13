import BuyAtBulk.EdgeOnlyGap.Items.FullBoundary
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofAAcyclicLeaf
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofAEdgeSubgraphEdges

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit even-subgraph cycle extraction, p. 4. -/
theorem evenSubgraphCycle (H : FiniteGraph) (z : Edges H → ZMod 2)
    (nonzero : z ≠ 0) (even : ∀ v, baseBoundary H z v = 0) :
  ∃ (v : Fin H.n) (w : H.graph.Walk v v), w.IsCycle ∧
    w.length ≤ (Finset.univ.filter fun e => z e ≠ 0).card ∧
    ∀ a ∈ w.edges, ∃ e : Edges H, a = s(e.val.1,e.val.2) ∧ z e ≠ 0 := by
  classical
  let W := Finset.univ.filter fun e => z e ≠ 0
  let G := edgeSubgraph H W
  have hW : W.Nonempty := by
    by_contra hn
    apply nonzero
    funext e
    have := Finset.not_nonempty_iff_eq_empty.mp hn
    by_contra he
    have hem : e ∈ W := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
    simpa [this] using hem
  have hne (e : Edges H) : e.val.1 ≠ e.val.2 := ne_of_lt e.prop.1
  have heq : ∀ (e f : Edges H),
      s(e.val.1,e.val.2) = s(f.val.1,f.val.2) → e = f := by
    intro e f h
    apply Subtype.ext
    rcases Sym2.eq_iff.mp h with h | h
    · exact Prod.ext h.1 h.2
    · have h1 := e.prop.1
      have h2 := f.prop.1
      rw [h.1, h.2] at h1
      exact False.elim ((lt_asymm h1 h2))
  have hacyc : ¬ G.IsAcyclic := by
    intro ha
    obtain ⟨e, he⟩ := hW
    have hadj : G.Adj e.val.1 e.val.2 := by
      simp only [G, edgeSubgraph, SimpleGraph.fromRel_adj]
      exact ⟨hne e, Or.inl ⟨e, he, rfl, rfl⟩⟩
    obtain ⟨u, v, huv, hleaf⟩ := ProofA.acyclicLeaf G ha hadj
    have huv' := huv
    simp only [G, edgeSubgraph, SimpleGraph.fromRel_adj] at huv'
    obtain ⟨f, hf, hfends⟩ : ∃ f ∈ W, s(u,v) = s(f.val.1,f.val.2) := by
      rcases huv'.2 with ⟨f, hf, rfl, rfl⟩ | ⟨f, hf, rfl, rfl⟩
      · exact ⟨f, hf, rfl⟩
      · exact ⟨f, hf, Sym2.eq_swap⟩
    have hincident : ∀ e ∈ W, (u = e.val.1 ∨ u = e.val.2) → e = f := by
      intro e he hi
      apply heq e f
      apply Eq.trans _ hfends
      rcases hi with rfl | rfl
      · have hv : e.val.2 = v := by
          apply hleaf
          simp only [G, edgeSubgraph, SimpleGraph.fromRel_adj]
          exact ⟨hne e, Or.inl ⟨e, he, rfl, rfl⟩⟩
        rw [hv]
      · have hv : e.val.1 = v := by
          apply hleaf
          simp only [G, edgeSubgraph, SimpleGraph.fromRel_adj]
          exact ⟨(hne e).symm, Or.inr ⟨e, he, rfl, rfl⟩⟩
        rw [hv, Sym2.eq_swap]
    have huf : u = f.val.1 ∨ u = f.val.2 := by
      rcases Sym2.eq_iff.mp hfends with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    have hsum : baseBoundary H z u = z f := by
      unfold baseBoundary
      rw [Finset.sum_eq_single f]
      · simp only [if_pos huf]
      · intro e _ hef
        by_cases hi : u = e.val.1 ∨ u = e.val.2
        · rw [if_pos hi]
          by_contra hz
          exact hef (hincident e (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩) hi)
        · exact if_neg hi
      · simp
    have hfz := (Finset.mem_filter.mp hf).2
    exact hfz (hsum.symm.trans (even u))
  obtain ⟨v, w, hw⟩ : ∃ v, ∃ w : G.Walk v v, w.IsCycle := by
    simpa only [SimpleGraph.IsAcyclic, not_forall, not_not] using hacyc
  have hle : G ≤ H.graph := by
    intro u v huv
    simp only [G, edgeSubgraph, SimpleGraph.fromRel_adj] at huv
    rcases huv.2 with ⟨e, he, rfl, rfl⟩ | ⟨e, he, rfl, rfl⟩
    · exact e.prop.2
    · exact e.prop.2.symm
  refine ⟨v, w.mapLe hle, hw.mapLe hle, ?_, ?_⟩
  · have hl := hw.isTrail.length_le_card_edgeFinset
    have hedge := ProofA.edgeSubgraphEdges H W
    change G.edgeFinset = _ at hedge
    rw [hedge, Finset.card_image_of_injective W heq] at hl
    simpa only [SimpleGraph.Walk.length_mapLe] using hl
  · intro a ha
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges] at ha
    have ham : a ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr (w.edges_subset_edgeSet ha)
    rw [ProofA.edgeSubgraphEdges H W] at ham
    rcases Finset.mem_image.mp ham with ⟨e, he, rfl⟩
    exact ⟨e, rfl, (Finset.mem_filter.mp he).2⟩


end BuyAtBulk.EdgeOnlyGap
