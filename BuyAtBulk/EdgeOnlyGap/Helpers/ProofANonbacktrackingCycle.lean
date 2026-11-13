import Mathlib.Combinatorics.SimpleGraph.Paths

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA

/-- A walk without an immediate reversal is a path or contains a no-longer cycle. -/
theorem pathOrCycle {V : Type*} {G : SimpleGraph V} {u v : V} (w : G.Walk u v)
    (nb : ∀ i : ℕ, i + 2 ≤ w.length → w.getVert i ≠ w.getVert (i + 2)) :
    w.IsPath ∨ ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ c.length ≤ w.length := by
  classical
  induction w with
  | nil => exact Or.inl SimpleGraph.Walk.IsPath.nil
  | @cons u v z h p ih =>
    have hnb : ∀ i : ℕ, i + 2 ≤ p.length → p.getVert i ≠ p.getVert (i + 2) := by
      intro i hi he
      apply nb (i + 1) (by simp only [SimpleGraph.Walk.length_cons]; omega)
      simpa only [SimpleGraph.Walk.getVert, Nat.add_assoc] using he
    rcases ih hnb with hp | ⟨a, c, hc, hlen⟩
    · by_cases hu : u ∈ p.support
      · right
        refine ⟨u, (p.takeUntil u hu).cons h, ?_, ?_⟩
        · apply (SimpleGraph.Walk.cons_isCycle_iff _ _).mpr
          refine ⟨hp.takeUntil hu, ?_⟩
          intro he
          have he' : s(v, u) ∈ (p.takeUntil u hu).edges := by
            simpa only [Sym2.eq_swap] using he
          have hlen := (hp.takeUntil hu).length_eq_one_of_mem_edges he'
          have hpu : p.getVert 1 = u := by
            simpa only [hlen] using SimpleGraph.Walk.getVert_length_takeUntil hu
          have hpge : 1 ≤ p.length := by
            have := p.length_takeUntil_le_length hu
            omega
          exact nb 0 (by simp only [SimpleGraph.Walk.length_cons]; omega)
            (by simpa only [SimpleGraph.Walk.getVert] using hpu.symm)
        · simp only [SimpleGraph.Walk.length_cons]
          exact Nat.add_le_add_right (p.length_takeUntil_le_length hu) 1
      · exact Or.inl (hp.cons hu)
    · exact Or.inr ⟨a, c, hc, le_trans hlen (by simp)⟩

end BuyAtBulk.EdgeOnlyGap.ProofA
