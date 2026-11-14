import BuyAtBulk.EdgeOnlyGap.Items.EdgeComponents
import Mathlib.Tactic

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

/-- A nonempty vertex set closed under the selected edges contains their entire
connected nonisolated support. -/
theorem connected_support_closed (G : FiniteGraph) (W : Finset (Edges G))
    (connected : edgeComponents G W = 1) (S : Finset (Fin G.n))
    (root : Fin G.n) (hr : root ∈ S) (hrW : root ∈ edgeSupport G W)
    (closed : ∀ e ∈ W, (e.val.1 ∈ S ∨ e.val.2 ∈ S) → e.val.1 ∈ S ∧ e.val.2 ∈ S) :
    edgeSupport G W ⊆ S := by
  have walkClosed : ∀ {u v : Fin G.n}, (edgeSubgraph G W).Walk u v → u ∈ S → v ∈ S := by
    intro u v w
    induction w with
    | nil => exact id
    | @cons u x v hadj rest ih =>
      intro hu
      apply ih
      simp only [edgeSubgraph,SimpleGraph.fromRel_adj] at hadj
      rcases hadj.2 with ⟨e,he,rfl,rfl⟩ | ⟨e,he,rfl,rfl⟩
      · exact (closed e he (Or.inl hu)).2
      · exact (closed e he (Or.inr hu)).1
  intro v hv
  have heq : (edgeSubgraph G W).connectedComponentMk root =
      (edgeSubgraph G W).connectedComponentMk v := by
    apply Finset.card_le_one.mp (le_of_eq connected)
    · exact Finset.mem_image_of_mem _ hrW
    · exact Finset.mem_image_of_mem _ hv
  obtain ⟨w⟩ := SimpleGraph.ConnectedComponent.eq.mp heq
  exact walkClosed w hr

end BuyAtBulk.EdgeOnlyGap.ProofA
