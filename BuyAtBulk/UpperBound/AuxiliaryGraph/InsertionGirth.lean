import BuyAtBulk.UpperBound.AuxiliaryGraph.Definitions
import BuyAtBulk.UpperBound.AuxiliaryGraph.CycleBypass

namespace BuyAtBulk.UpperBound.AuxiliaryGraph
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Every edge except the newly inserted unordered pair was already present. -/
theorem old_edge_of_new (edges : List (AuxiliaryEdge G)) (inserted : AuxiliaryEdge G)
    (scale : ℚ) {e : Sym2 V} (member : e ∈ (atScale (inserted :: edges) scale).edgeSet)
    (different : e ≠ key inserted) : e ∈ (atScale edges scale).edgeSet := by
  simp only [atScale, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff, Set.mem_ofPred_eq] at member ⊢
  obtain ⟨⟨record, hrecord, hscale, heq⟩, nonloop⟩ := member
  cases List.mem_cons.mp hrecord with
  | inl hcur => subst record; exact (different heq).elim
  | inr hold => exact ⟨⟨record, hold, hscale, heq⟩, nonloop⟩

theorem atScale_cons_of_ne (edges : List (AuxiliaryEdge G)) (inserted : AuxiliaryEdge G)
    (scale : ℚ) (different : inserted.scale ≠ scale) :
    atScale (inserted :: edges) scale = atScale edges scale := by
  ext u v
  constructor
  · rintro ⟨⟨record, member, hscale, heq⟩, huv⟩
    cases List.mem_cons.mp member with
    | inl hcur => subst record; exact (different hscale).elim
    | inr hold => exact ⟨⟨record, hold, hscale, heq⟩, huv⟩
  · rintro ⟨⟨record, member, hscale, heq⟩, huv⟩
    exact ⟨⟨record, List.mem_cons_of_mem _ member, hscale, heq⟩, huv⟩

/-- Inserting an edge with no short old endpoint bypass preserves high girth.
The cycle proof explicitly extracts a bypass from any alleged new short cycle. -/
theorem highGirth_cons (edges : List (AuxiliaryEdge G)) (inserted : AuxiliaryEdge G)
    {r : ℕ} (distinct : inserted.source ≠ inserted.target)
    (old : ∀ scale, Girth.HighGirth (atScale edges scale) r)
    (noBypass : ∀ walk : (atScale edges inserted.scale).Walk inserted.source inserted.target,
      walk.length + 1 ≤ 2 * r → False) :
    ∀ scale, Girth.HighGirth (atScale (inserted :: edges) scale) r := by
  intro scale
  by_cases hscale : inserted.scale = scale
  · subst scale
    intro root cycle hc
    by_contra hnot
    have hshort : cycle.length ≤ 2 * r := by omega
    by_cases hedge : key inserted ∈ cycle.edges
    · obtain ⟨bypass, avoids, shorter, subset⟩ := cycle_bypass_edge cycle hc distinct hedge
      have allowed : ∀ e ∈ bypass.edges, e ∈ (atScale edges inserted.scale).edgeSet := by
        intro e he
        apply old_edge_of_new edges inserted inserted.scale (bypass.edges_subset_edgeSet he)
        intro heq
        have hnew : key inserted ∈ bypass.edges := by rw [← heq]; exact he
        exact avoids hnew
      apply noBypass (bypass.transfer _ allowed)
      simpa only [SimpleGraph.Walk.length_transfer] using shorter.trans hshort
    · have allowed : ∀ e ∈ cycle.edges, e ∈ (atScale edges inserted.scale).edgeSet := by
        intro e he
        apply old_edge_of_new edges inserted inserted.scale (cycle.edges_subset_edgeSet he)
        intro heq
        exact hedge (heq ▸ he)
      have hbound := old inserted.scale root (cycle.transfer _ allowed) (hc.transfer allowed)
      have hlength : (cycle.transfer _ allowed).length = cycle.length :=
        SimpleGraph.Walk.length_transfer cycle allowed
      omega
  · rw [atScale_cons_of_ne edges inserted scale hscale]
    exact old scale

/-- The chronological unordered edge list at one scale. -/
def keysAtScale (edges : List (AuxiliaryEdge G)) (scale : ℚ) : List (Sym2 V) :=
  (edges.filter fun edge => edge.scale = scale).map key

theorem no_duplicate_key (edges : List (AuxiliaryEdge G)) (inserted : AuxiliaryEdge G)
    {r : ℕ} (hr : 1 ≤ r) (distinct : inserted.source ≠ inserted.target)
    (noBypass : ∀ walk : (atScale edges inserted.scale).Walk inserted.source inserted.target,
      walk.length + 1 ≤ 2 * r → False) : key inserted ∉ keysAtScale edges inserted.scale := by
  intro member
  obtain ⟨record, hrecord, heq⟩ := List.mem_map.mp member
  obtain ⟨hold, scale⟩ := List.mem_filter.mp hrecord
  have hscale : record.scale = inserted.scale := by simpa using scale
  have adjacent : (atScale edges inserted.scale).Adj inserted.source inserted.target :=
    ⟨⟨record, hold, hscale, heq.symm⟩, distinct⟩
  exact noBypass adjacent.toWalk (by simp; omega)

theorem nodup_cons (edges : List (AuxiliaryEdge G)) (inserted : AuxiliaryEdge G)
    {r : ℕ} (hr : 1 ≤ r) (distinct : inserted.source ≠ inserted.target)
    (old : ∀ scale, (keysAtScale edges scale).Nodup)
    (noBypass : ∀ walk : (atScale edges inserted.scale).Walk inserted.source inserted.target,
      walk.length + 1 ≤ 2 * r → False) :
    ∀ scale, (keysAtScale (inserted :: edges) scale).Nodup := by
  intro scale
  by_cases hscale : inserted.scale = scale
  · subst scale
    have hlist : keysAtScale (inserted :: edges) inserted.scale =
        key inserted :: keysAtScale edges inserted.scale := by simp [keysAtScale]
    rw [hlist, List.nodup_cons]
    exact ⟨no_duplicate_key edges inserted hr distinct noBypass, old inserted.scale⟩
  · simpa [keysAtScale, hscale] using old scale

end BuyAtBulk.UpperBound.AuxiliaryGraph
