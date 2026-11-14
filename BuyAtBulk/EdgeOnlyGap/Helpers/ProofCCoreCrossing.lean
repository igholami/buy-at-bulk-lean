import BuyAtBulk.EdgeOnlyGap.Items.SupplyData
import BuyAtBulk.EdgeOnlyGap.Items.RegularBase
import BuyAtBulk.EdgeOnlyGap.Helpers.EdgeCard

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 3, implicit: every supply-graph path between two distinct
hubs leaves its first hub by a spoke and then must traverse a core (lift) edge. -/
theorem proofC_coreCrossing (H : FiniteGraph) (q : ℕ) (π : Lift H q) :
    ∀ {s t : SupplyVertex H q} (w : (supplyGraph H q π).Walk s t) (u v : Fin H.n),
      s = Sum.inl u → t = Sum.inl v → u ≠ v → w.IsPath →
      ∃ a b : Fin H.n × Fin q, s(Sum.inr a, Sum.inr b) ∈ w.edges := by
  intro s t w u v hs ht huv hp
  subst hs ht
  cases w with
  | nil => exact absurd rfl huv
  | cons h₁ w' =>
    rename_i x
    rw [supplyGraph, SimpleGraph.fromRel_adj] at h₁
    obtain ⟨-, h₁⟩ := h₁
    -- x is a copy of u
    obtain ⟨j, rfl⟩ : ∃ j, x = Sum.inr (u, j) := by
      rcases h₁ with (⟨v', j, h1, h2⟩ | ⟨a, b, h1, -, -⟩) | (⟨v', j, h1, h2⟩ | ⟨a, b, -, h2, -⟩)
      · cases h1; exact ⟨j, h2⟩
      · cases h1
      · cases h2
      · cases h2
    cases w' with
    | cons h₂ w'' =>
      rename_i y
      have hnot : y ≠ Sum.inl u := by
        intro hy
        subst hy
        have hp' := hp
        rw [SimpleGraph.Walk.cons_isPath_iff] at hp'
        apply hp'.2
        simp
      rw [supplyGraph, SimpleGraph.fromRel_adj] at h₂
      obtain ⟨-, h₂⟩ := h₂
      rcases h₂ with (⟨v', j', h1, h2⟩ | ⟨a, b, h1, h2, -⟩) | (⟨v', j', h1, h2⟩ | ⟨a, b, h1, h2, -⟩)
      · cases h1
      · cases h1; subst h2
        exact ⟨(u, j), b, by simp⟩
      · first
          | exact absurd rfl hnot
          | (cases h2; subst h1; exact absurd rfl hnot)
      · cases h2; subst h1
        exact ⟨(u, j), a, by simp⟩

/-- Handshaking for a `d`-regular base graph in request coordinates. -/
theorem proofC_requestsHandshake (H : FiniteGraph) (d g : ℕ) (base : RegularBase H d g) :
    2 * requests H = H.n * d := by
  classical
  have h := H.graph.sum_degrees_eq_twice_card_edges
  simp only [base.2.1, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at h
  unfold requests
  rw [edgeCard H]
  simpa [SimpleGraph.edgeFinset, mul_comm] using h.symm

end BuyAtBulk.EdgeOnlyGap
