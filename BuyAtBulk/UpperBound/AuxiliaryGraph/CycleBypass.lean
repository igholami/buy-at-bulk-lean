import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

namespace BuyAtBulk.UpperBound.AuxiliaryGraph
open SimpleGraph
variable {V : Type} [DecidableEq V] {H : SimpleGraph V}

/-- Removing an edge of an actual cycle leaves an endpoint-to-endpoint walk
using only other cycle edges, with one fewer edge. The proof chooses the one
of the two cycle arcs which avoids the designated edge. -/
theorem cycle_bypass_edge {root a b : V} (cycle : H.Walk root root)
    (hc : cycle.IsCycle) (distinct : a ≠ b) (edge : s(a, b) ∈ cycle.edges) :
    ∃ bypass : H.Walk a b, s(a, b) ∉ bypass.edges ∧ bypass.length + 1 ≤ cycle.length ∧
      ∀ e ∈ bypass.edges, e ∈ cycle.edges := by
  have ha : a ∈ cycle.support := cycle.fst_mem_support_of_mem_edges edge
  let rotated := cycle.rotate a ha
  have hrotated : rotated.IsCycle := hc.rotate ha
  have hb : b ∈ rotated.support := by
    simpa [rotated] using cycle.snd_mem_support_of_mem_edges edge
  let first := rotated.takeUntil b hb
  let second := rotated.dropUntil b hb
  have hdisjoint : first.edges.Disjoint second.edges :=
    hrotated.isTrail.disjoint_edges_takeUntil_dropUntil hb
  have hfirstnonempty : ¬ first.Nil := SimpleGraph.Walk.not_nil_of_ne distinct
  have hsecondnonempty : ¬ second.Nil := SimpleGraph.Walk.not_nil_of_ne distinct.symm
  have hfirstpos := SimpleGraph.Walk.not_nil_iff_lt_length.mp hfirstnonempty
  have hsecondpos := SimpleGraph.Walk.not_nil_iff_lt_length.mp hsecondnonempty
  have hlength : first.length + second.length = cycle.length := by
    have heq := congrArg SimpleGraph.Walk.length (rotated.take_spec hb)
    rw [SimpleGraph.Walk.length_append] at heq
    change first.length + second.length = rotated.length at heq
    exact heq.trans (cycle.length_rotate a ha)
  have hfirstsubset : ∀ e ∈ first.edges, e ∈ cycle.edges := by
    intro e he
    exact (cycle.rotate_edges a ha).mem_iff.mp (rotated.edges_takeUntil_subset_edges hb he)
  have hsecondsubset : ∀ e ∈ second.edges, e ∈ cycle.edges := by
    intro e he
    exact (cycle.rotate_edges a ha).mem_iff.mp (rotated.edges_dropUntil_subset_edges hb he)
  by_cases hfirst : s(a, b) ∈ first.edges
  · refine ⟨second.reverse, ?_, ?_, ?_⟩
    · intro hsecond
      have he : s(a, b) ∈ second.edges := by simpa using hsecond
      exact hdisjoint hfirst he
    · simp only [SimpleGraph.Walk.length_reverse]
      omega
    · intro e he
      apply hsecondsubset e
      simpa using he
  · exact ⟨first, hfirst, by omega, hfirstsubset⟩

end BuyAtBulk.UpperBound.AuxiliaryGraph
