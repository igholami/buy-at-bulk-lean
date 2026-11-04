import BuyAtBulk.UpperBound.AuxiliaryGraph.InsertionGirth

namespace BuyAtBulk.UpperBound.AuxiliaryGraph
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

@[simp] theorem activeVertices_mem (edges : List (AuxiliaryEdge G)) (scale : ℚ) (v : V) :
    v ∈ activeVertices edges scale ↔ ∃ edge ∈ edges,
      edge.scale = scale ∧ (v = edge.source ∨ v = edge.target) := by
  classical
  simp [activeVertices, and_assoc]

theorem active_subset_eligible (state : RoundingState G) (eligible : EdgesEligible G state)
    (scale : ℚ) : activeVertices state.edges scale ⊆ eligibleVertices state.centers scale := by
  intro v hv
  obtain ⟨edge, member, sameScale, endpoint⟩ := (activeVertices_mem _ _ _).mp hv
  obtain ⟨hs, ht⟩ := eligible edge member
  rw [eligibleVertices_mem]
  cases endpoint with
  | inl heq => subst v; simpa only [sameScale] using hs
  | inr heq => subst v; simpa only [sameScale] using ht

theorem active_card_le_births (state : RoundingState G) (eligible : EdgesEligible G state)
    (scale : ℚ) : (activeVertices state.edges scale).card ≤
      (state.centers.filter fun record => scale ≤ record.birthScale).length := by
  classical
  calc
    _ ≤ (eligibleVertices state.centers scale).card :=
      Finset.card_le_card (active_subset_eligible state eligible scale)
    _ ≤ ((state.centers.filter fun record => scale ≤ record.birthScale).map CenterRecord.endpoint).length :=
      List.toFinset_card_le _
    _ = _ := List.length_map _

theorem graph_support_active (edges : List (AuxiliaryEdge G)) (scale : ℚ) :
    (atScale edges scale).support ⊆ (activeVertices edges scale : Set V) := by
  intro v hv
  obtain ⟨w, adjacent⟩ := hv
  obtain ⟨⟨record, member, sameScale, endpoints⟩, distinct⟩ := adjacent
  have hmem : v ∈ key record := by rw [← endpoints]; simp
  exact (activeVertices_mem edges scale v).mpr
    ⟨record, member, sameScale, Sym2.mem_iff.mp hmem⟩

/-- Remove isolated physical vertices before counting auxiliary graph vertices. -/
noncomputable abbrev activeGraph (edges : List (AuxiliaryEdge G)) (scale : ℚ) :
    SimpleGraph {v : V // v ∈ (activeVertices edges scale : Set V)} := (atScale edges scale).induce (activeVertices edges scale : Set V)

theorem activeGraph_vertices_card (edges : List (AuxiliaryEdge G)) (scale : ℚ) :
    Fintype.card {v : V // v ∈ (activeVertices edges scale : Set V)} = (activeVertices edges scale).card := by
  classical
  exact Fintype.card_of_subtype (activeVertices edges scale) (by intro v; rfl)

theorem activeGraph_card_edges (edges : List (AuxiliaryEdge G)) (scale : ℚ) :
    Nat.card (activeGraph edges scale).edgeSet = Nat.card (atScale edges scale).edgeSet := by
  classical
  have heq := (atScale edges scale).card_edgeFinset_induce_of_support_subset (graph_support_active edges scale)
  simpa only [activeGraph, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using heq

private theorem edge_mem_keys (edges : List (AuxiliaryEdge G)) (scale : ℚ) {e : Sym2 V}
    (member : e ∈ (atScale edges scale).edgeSet) : e ∈ keysAtScale edges scale := by
  simp only [atScale, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff, Set.mem_ofPred_eq] at member
  obtain ⟨⟨record, hrecord, sameScale, heq⟩, nonloop⟩ := member
  apply List.mem_map.mpr
  refine ⟨record, ?_, heq.symm⟩
  simpa using And.intro hrecord sameScale

private theorem key_mem_edges (edges : List (AuxiliaryEdge G)) (scale : ℚ)
    (distinct : ∀ edge ∈ edges, edge.source ≠ edge.target) {e : Sym2 V}
    (member : e ∈ keysAtScale edges scale) : e ∈ (atScale edges scale).edgeSet := by
  obtain ⟨record, hrecord, heq⟩ := List.mem_map.mp member
  have hm : record ∈ edges ∧ record.scale = scale := by simpa using hrecord
  subst e
  change (atScale edges scale).Adj record.source record.target
  exact ⟨⟨record, hm.1, hm.2, rfl⟩, distinct record hm.1⟩

/-- Unordered-record simplicity and nonloops justify identifying the paid
record count with the edge count of the actual simple auxiliary graph. -/
theorem paid_count_eq_edges (edges : List (AuxiliaryEdge G)) (scale : ℚ)
    (distinct : ∀ edge ∈ edges, edge.source ≠ edge.target)
    (nodup : (keysAtScale edges scale).Nodup) :
    (edges.filter fun edge => edge.scale = scale).length = Nat.card (activeGraph edges scale).edgeSet := by
  classical
  have hfin : (atScale edges scale).edgeFinset = (keysAtScale edges scale).toFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, List.mem_toFinset]
    exact ⟨edge_mem_keys edges scale, key_mem_edges edges scale distinct⟩
  rw [activeGraph_card_edges, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, hfin,
    List.toFinset_card_of_nodup nodup]
  simp [keysAtScale]

end BuyAtBulk.UpperBound.AuxiliaryGraph
