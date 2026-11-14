import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-! Walk and cycle surgery used in the proof of the Erdős–Sachs theorem. -/

namespace BuyAtBulk.EdgeOnlyGap.ErdosSachs

open SimpleGraph

variable {V : Type*}

/-- A cycle through the edge `ab` yields a walk from `b` to `a` that avoids `ab`, uses only
edges of the cycle, and is one step shorter. -/
theorem cycle_edge_walk {G : SimpleGraph V} {w a b : V} (c : G.Walk w w) (hc : c.IsCycle)
    (he : s(a, b) ∈ c.edges) :
    ∃ W : G.Walk b a, s(a, b) ∉ W.edges ∧ (∀ e ∈ W.edges, e ∈ c.edges) ∧
      W.length + 1 = c.length := by
  classical
  have ha : a ∈ c.support := c.fst_mem_support_of_mem_edges he
  set R := c.rotate a ha with hR
  have hRc : R.IsCycle := hc.rotate ha
  have hRe : ∀ e, e ∈ R.edges ↔ e ∈ c.edges := fun e => (c.rotate_edges a ha).mem_iff
  have hRl : R.length = c.length := Walk.length_rotate c a ha
  clear_value R
  cases R with
  | nil => exact absurd hRc (by simp [Walk.isCycle_def])
  | @cons _ a' _ h p =>
    rw [Walk.cons_isCycle_iff] at hRc
    obtain ⟨hp, hnot⟩ := hRc
    have heR : s(a, b) ∈ (Walk.cons h p).edges := (hRe _).2 he
    rw [Walk.edges_cons, List.mem_cons] at heR
    rcases heR with heq | hin
    · -- the cycle leaves `a` along `ab`
      have hb : b = a' := by
        rcases Sym2.eq_iff.mp heq with ⟨-, h2⟩ | ⟨h1, h2⟩
        · exact h2
        · exact absurd h1 (G.ne_of_adj h)
      subst hb
      refine ⟨p, hnot, fun e he' => (hRe e).1 (by simp [he']), ?_⟩
      simpa using hRl
    · -- the cycle returns to `a` along `ba`
      have hpr : p.reverse.IsPath := hp.reverse
      have hin' : s(a, b) ∈ p.reverse.edges := by simpa using hin
      generalize hr : p.reverse = r at hpr hin'
      cases r with
      | nil => exact absurd h G.irrefl
      | @cons _ c' _ h2 q =>
        rw [Walk.cons_isPath_iff] at hpr
        obtain ⟨-, haq⟩ := hpr
        rw [Walk.edges_cons, List.mem_cons] at hin'
        have hc' : c' = b := by
          rcases hin' with heq | hq
          · rcases Sym2.eq_iff.mp heq with ⟨-, h2'⟩ | ⟨h1, -⟩
            · exact h2'.symm
            · exact absurd h1 (G.ne_of_adj h2)
          · exact absurd (q.fst_mem_support_of_mem_edges hq) haq
        subst hc'
        have hqe : ∀ e ∈ q.edges, e ∈ p.edges := by
          intro e he'
          have : e ∈ p.reverse.edges := by rw [hr]; simp [he']
          simpa using this
        have hne : s(a, c') ≠ s(a', a) := by
          intro heq
          apply hnot
          rw [heq, Sym2.eq_swap] at hin
          exact hin
        refine ⟨q.concat h.symm, ?_, ?_, ?_⟩
        · rw [Walk.edges_concat, List.concat_eq_append, List.mem_append, not_or]
          refine ⟨fun hq => haq (q.fst_mem_support_of_mem_edges hq), ?_⟩
          simpa using hne
        · intro e he'
          rw [Walk.edges_concat, List.concat_eq_append, List.mem_append] at he'
          apply (hRe e).1
          rcases he' with hq | hl
          · simp [hqe e hq]
          · simp at hl; subst hl; simp [Sym2.eq_swap]
        · have hlen : (Walk.cons h2 q).length = p.length := by rw [← hr]; simp
          rw [Walk.length_concat, ← hRl]
          simp only [Walk.length_cons] at hlen ⊢
          omega

/-- Splitting a walk at the uses of one extra edge `pq`: either the walk already lives in `K`,
or it decomposes into two `K`-walks to and from the two endpoints of `pq`. -/
theorem walk_split (K : SimpleGraph V) {G : SimpleGraph V} (p q : V) :
    ∀ {a b : V} (W : G.Walk a b), (∀ e ∈ W.edges, e ∈ K.edgeSet ∨ e = s(p, q)) →
      (∃ W' : K.Walk a b, W'.length ≤ W.length) ∨
      (∃ (p₁ q₁ : V) (W₁ : K.Walk a p₁) (W₂ : K.Walk q₁ b),
        ((p₁ = p ∧ q₁ = q) ∨ (p₁ = q ∧ q₁ = p)) ∧ W₁.length + W₂.length + 1 ≤ W.length)
  | _, _, .nil, _ => Or.inl ⟨.nil, le_rfl⟩
  | a, b, .cons (v := a') h W, hW => by
    have hfirst := hW s(a, a') (by simp)
    have hrest : ∀ e ∈ W.edges, e ∈ K.edgeSet ∨ e = s(p, q) :=
      fun e he => hW e (by simp [he])
    have hpq : s(a, a') ∈ K.edgeSet → K.Adj a a' := fun h' => h'
    rcases walk_split K p q W hrest with ⟨W₁, hl⟩ | ⟨p₁, q₁, W₁, W₂, hs, hl⟩
    · rcases hfirst with hk | heq
      · exact Or.inl ⟨.cons (hpq hk) W₁, by simp; omega⟩
      · refine Or.inr ⟨a, a', .nil, W₁, ?_, by simp; omega⟩
        rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, h2⟩
    · rcases hfirst with hk | heq
      · exact Or.inr ⟨p₁, q₁, .cons (hpq hk) W₁, W₂, hs, by simp; omega⟩
      · have hq₁ : q₁ = a ∨ q₁ = a' := by
          rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
            rcases hs with ⟨-, h3⟩ | ⟨-, h3⟩ <;> subst h1 h2 <;> simp [h3]
        rcases hq₁ with rfl | rfl
        · exact Or.inl ⟨W₂, by simp; omega⟩
        · refine Or.inr ⟨a, q₁, .nil, W₂, ?_, by simp; omega⟩
          rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨h1, h2⟩

/-- In a graph all of whose cycles have length at least `g`, every walk between the ends of an
edge `xy` that avoids `xy` has length at least `g - 1`. -/
theorem girth_avoid {G : SimpleGraph V} {g : ℕ}
    (hG : ∀ a (c : G.Walk a a), c.IsCycle → g ≤ c.length) {x y : V} (hxy : G.Adj x y)
    (W : G.Walk x y) (hW : s(x, y) ∉ W.edges) : g ≤ W.length + 1 := by
  classical
  have hP := W.bypass_isPath
  have hcyc : (Walk.cons hxy.symm W.bypass).IsCycle := by
    rw [Walk.cons_isCycle_iff]
    refine ⟨hP, fun h => hW ?_⟩
    rw [Sym2.eq_swap]
    exact W.edges_bypass_subset_edges h
  have := hG _ _ hcyc
  simp only [Walk.length_cons] at this
  have := W.length_bypass_le_length
  omega

/-- A walk in `G.deleteEdges {e}` is a walk in `G` of the same length avoiding `e`. -/
theorem deleteEdges_walk {G : SimpleGraph V} {e : Sym2 V} {a b : V}
    (W : (G.deleteEdges {e}).Walk a b) :
    ∃ W' : G.Walk a b, W'.length = W.length ∧ e ∉ W'.edges := by
  refine ⟨W.mapLe (G.deleteEdges_le _), Walk.length_mapLe _ _, ?_⟩
  rw [Walk.edges_mapLe_eq_edges]
  intro h
  have := W.edges_subset_edgeSet h
  rw [edgeSet_deleteEdges] at this
  exact this.2 rfl

end BuyAtBulk.EdgeOnlyGap.ErdosSachs
