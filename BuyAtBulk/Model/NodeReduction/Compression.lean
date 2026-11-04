import BuyAtBulk.Model.NodeReduction.Embedding

namespace BuyAtBulk.NodeReduction
open SimpleGraph

/-- Every simple path between old vertices in the subdivision graph compresses
back to an original simple path with exactly the same node/edge incidences.
Internal endpoint leaves are ruled out by simplicity, rather than assumed absent. -/
def compressPathFuel (D : GraphData) (fuel : ℕ) {u v : D.Vertex}
    (p : (graph D).Walk (.original u) (.original v)) (hp : p.IsPath) (hlen : p.length ≤ fuel) :
    { q : D.graph.Walk u v // q.IsPath ∧
      (∀ w, w ∈ q.support ↔ Vertex.original w ∈ p.support) ∧
      (∀ e, e ∈ q.edges ↔ Vertex.edge e ∈ p.support) } := by
  classical
  cases fuel with
  | zero =>
    cases p with
    | nil => exact ⟨.nil, .nil, by intro w; simp, by intro e; simp⟩
    | cons hadj tail => simp at hlen
  | succ fuel =>
    cases p with
    | nil => exact ⟨.nil, .nil, by intro w; simp, by intro e; simp⟩
    | @cons _ next _ hadj tail =>
      cases next with
      | original w => simp [graph] at hadj
      | leaf i side =>
        cases tail with
        | @cons _ next _ hleaf rest =>
          have hnext : next = Vertex.original (endpoint D i side) :=
            (leaf_neighbor_iff D i side next).mp hleaf
          have hu : u = endpoint D i side := hadj
          have heq : next = Vertex.original u := hnext.trans (congrArg Vertex.original hu.symm)
          cases heq
          have hs := hp.support_nodup
          simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hs
          exact (hs.1 (by simp)).elim
      | edge e =>
        cases tail with
        | @cons _ next _ hnext rest =>
          cases next with
          | edge f => simp [graph] at hnext
          | leaf i side => simp [graph] at hnext
          | original w =>
            have hu : e ∈ D.graph.edgeSet ∧ u ∈ e := hadj
            have hw : e ∈ D.graph.edgeSet ∧ w ∈ e := hnext
            have hs := hp.support_nodup
            simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hs
            have hne : u ≠ w := by
              intro heq
              subst w
              exact hs.1 (by simp)
            have heqedge : e = s(u, w) := (Sym2.mem_and_mem_iff hne).mp ⟨hu.2, hw.2⟩
            have hold : D.graph.Adj u w := by simpa [heqedge] using hu.1
            have hrest : rest.length ≤ fuel := by
              simp only [SimpleGraph.Walk.length_cons] at hlen
              omega
            let result := compressPathFuel D fuel rest hp.of_cons.of_cons hrest
            let q := result.val
            have hq := result.property.1
            have hnodes := result.property.2.1
            have hedges := result.property.2.2
            have hnot : u ∉ q.support := by
              intro hmem
              apply hs.1
              simp only [List.mem_cons]
              exact Or.inr ((hnodes u).mp hmem)
            refine ⟨.cons hold q, hq.cons hnot, ?_, ?_⟩
            · intro z
              simp [q, hnodes z]
            · intro f
              simp [q, hedges f, heqedge]
termination_by fuel

/-- Recursive path compression with initial fuel equal to the actual walk
length. Each original-edge step consumes two subdivision incidences. -/
def compressPath (D : GraphData) {u v : D.Vertex}
    (p : (graph D).Walk (.original u) (.original v)) (hp : p.IsPath) :
    { q : D.graph.Walk u v // q.IsPath ∧
      (∀ w, w ∈ q.support ↔ Vertex.original w ∈ p.support) ∧
      (∀ e, e ∈ q.edges ↔ Vertex.edge e ∈ p.support) } :=
  compressPathFuel D p.length p hp (le_refl _)

/-- Compression does not increase the length of the actual returned walk. -/
theorem compressPath_length_le (D : GraphData) {u v : D.Vertex}
    (p : (graph D).Walk (.original u) (.original v)) (hp : p.IsPath) :
    (compressPath D p hp).val.length ≤ p.length := by
  let result := compressPath D p hp
  have nodup : (result.val.support.map (Vertex.original (D := D))).Nodup :=
    List.Nodup.map (fun _ _ equal => Vertex.original.inj equal) result.property.1.support_nodup
  have subset : result.val.support.map (Vertex.original (D := D)) ⊆ p.support := by
    intro vertex member
    obtain ⟨w, supported, rfl⟩ := List.mem_map.mp member
    exact (result.property.2.1 w).mp supported
  have length := nodup.length_le_of_subset subset
  simp only [List.length_map, Walk.length_support] at length
  exact Nat.add_le_add_iff_right.mp length

/-- Logical existence follows from the actual recursive compressor. -/
theorem exists_compressed (D : GraphData) {u v : D.Vertex}
    (p : (graph D).Walk (.original u) (.original v)) (hp : p.IsPath) :
    ∃ q : D.graph.Walk u v, q.IsPath ∧
      (∀ w, w ∈ q.support ↔ Vertex.original w ∈ p.support) ∧
      (∀ e, e ∈ q.edges ↔ Vertex.edge e ∈ p.support) :=
  ⟨(compressPath D p hp).val, (compressPath D p hp).property⟩

end BuyAtBulk.NodeReduction
