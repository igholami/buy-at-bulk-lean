import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace BuyAtBulk.EdgeOnlyGap.ProofA

/-- A finite forest with an edge has a vertex with exactly one neighbor. -/
theorem acyclicLeaf {V : Type*} [Finite V] (G : SimpleGraph V)
    (ha : G.IsAcyclic) {a b : V} (hab : G.Adj a b) :
    ∃ u v, G.Adj u v ∧ ∀ w, G.Adj u w → w = v := by
  classical
  letI : Nonempty V := ⟨a⟩
  obtain ⟨u, v, p, hp, hmax⟩ := SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  have hlen : 1 ≤ p.length := by
    have h := hmax a b (SimpleGraph.Walk.cons hab SimpleGraph.Walk.nil) (by simp [hab.ne])
    simpa using h
  have hnil : ¬ p.Nil := by
    intro h
    have : p.length = 0 := SimpleGraph.Walk.length_eq_zero_iff.mpr h
    omega
  refine ⟨u, p.snd, p.adj_snd hnil, ?_⟩
  intro w hw
  apply ha.eq_snd_of_adj_start hp hw
  by_contra hn
  have hpath := hp.cons hn (h := hw.symm)
  have h := hmax w v (p.cons hw.symm) hpath
  simp only [SimpleGraph.Walk.length_cons] at h
  omega

end BuyAtBulk.EdgeOnlyGap.ProofA
