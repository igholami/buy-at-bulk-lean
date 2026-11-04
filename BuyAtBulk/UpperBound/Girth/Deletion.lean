import BuyAtBulk.UpperBound.Girth.Counting
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Tactic.Linarith

namespace BuyAtBulk.UpperBound.Girth
open SimpleGraph

/-- Induced subgraphs cannot introduce a short cycle. -/
theorem highGirth_induce {V : Type} {G : SimpleGraph V} {r : ℕ}
    (hg : HighGirth G r) (s : Set V) : HighGirth (G.induce s) r := by
  intro v p hp
  have hc : (p.map (SimpleGraph.Embedding.induce (G := G) s).toHom).IsCycle :=
    hp.map (SimpleGraph.Embedding.induce (G := G) s).injective
  exact lt_of_lt_of_eq (hg v.val _ hc)
    (SimpleGraph.Walk.length_map (SimpleGraph.Embedding.induce (G := G) s).toHom p)

/-- The Moore bound forces a low-degree vertex without assuming a pruning
certificate or a breadth-first expansion as an input hypothesis. -/
theorem exists_low_degree {V : Type} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} {r d N : ℕ} (hr : 1 ≤ r) (hg : HighGirth G r)
    (hn : Fintype.card V ≤ N) (hpow : N < d ^ r) :
    ∃ v, Nat.card (G.neighborSet v) ≤ d := by
  classical
  by_contra hnolow
  have hd : ∀ v, d + 1 ≤ Nat.card (G.neighborSet v) := by
    intro v
    have hnot : ¬ Nat.card (G.neighborSet v) ≤ d := fun hv => hnolow ⟨v, hv⟩
    omega
  have hm := moore_bound hr hg hd (Classical.choice ‹Nonempty V›)
  simp only [Nat.add_sub_cancel] at hm
  omega

/-- Repeated low-degree deletion bounds the number of graph edges. The
integer threshold is chosen later from the real `r`th root of the vertex count. -/
theorem edge_bound_integer {V : Type} [Fintype V] (G : SimpleGraph V)
    {r d N : ℕ} (hr : 1 ≤ r) (hg : HighGirth G r)
    (hn : Fintype.card V ≤ N) (hpow : N < d ^ r) :
    Nat.card G.edgeSet ≤ Fintype.card V * d := by
  classical
  by_cases hzero : Fintype.card V = 0
  · have : IsEmpty V := Fintype.card_eq_zero_iff.mp hzero
    simp [Nat.card_eq_fintype_card]
  · have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨v, hv⟩ := exists_low_degree hr hg hn hpow
    let s : Set V := ({v} : Set V)ᶜ
    let H := G.induce s
    have hcard : Fintype.card s = Fintype.card V - 1 := by
      have hsingle : Fintype.card ({v} : Set V) = 1 := Fintype.card_unique
      simpa only [s, hsingle] using (Fintype.card_compl_set ({v} : Set V))
    have hnH : Fintype.card s ≤ N := by rw [hcard]; omega
    have hIH : Nat.card H.edgeSet ≤ Fintype.card s * d :=
      edge_bound_integer H hr (highGirth_induce hg s) hnH hpow
    have hdeg : G.degree v ≤ d := by
      simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using hv
    have hedge : G.edgeFinset.card = H.edgeFinset.card + G.degree v := by
      have heq := G.card_edgeFinset_induce_compl_singleton v
      have hdel := G.card_edgeFinset_deleteIncidenceSet v
      have hle := G.degree_le_card_edgeFinset v
      change H.edgeFinset.card = (G.deleteIncidenceSet v).edgeFinset.card at heq
      omega
    have hnatG : Nat.card G.edgeSet = G.edgeFinset.card := by
      rw [Nat.card_eq_fintype_card, edgeFinset_card]
    have hnatH : Nat.card H.edgeSet = H.edgeFinset.card := by
      rw [Nat.card_eq_fintype_card, edgeFinset_card]
    rw [hnatG, hedge]
    rw [hnatH] at hIH
    have hcardadd : Fintype.card V = Fintype.card s + 1 := by omega
    nlinarith
termination_by Fintype.card V

decreasing_by
  classical
  change Fintype.card s < Fintype.card V
  rw [hcard]
  omega

end BuyAtBulk.UpperBound.Girth
