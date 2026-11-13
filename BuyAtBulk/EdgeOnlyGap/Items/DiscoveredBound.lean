import BuyAtBulk.EdgeOnlyGap.Items.DFSEdges

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

private lemma dfsStep_visited_card (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (π : Lift H q) (st₀ st₁ : DFSState H q) (s : DFSSymbol d)
    (h : dfsStep H q d ports π st₀ s = some st₁) :
    st₁.visited.card ≤ st₀.visited.card + (if s.isSome then 1 else 0) := by
  unfold dfsStep at h
  cases hstack : st₀.stack with
  | nil => simp [hstack] at h
  | cons x xs =>
    rw [hstack] at h
    cases s with
    | none =>
      dsimp at h
      split_ifs at h
      cases h
      simp
    | some pflag =>
      rcases pflag with ⟨p, newFlag⟩
      dsimp at h
      cases hport : ports.port x.1 p with
      | none => simp [hport] at h
      | some e =>
        rw [hport] at h
        dsimp at h
        split_ifs at h
        all_goals
          cases h
          simp only [Option.isSome_some, ↓reduceIte]
          exact Finset.card_insert_le _ _

private lemma foldlM_visited_card (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (π : Lift H q) (script : List (DFSSymbol d)) :
    ∀ (st₀ st : DFSState H q),
      script.foldlM (dfsStep H q d ports π) st₀ = some st →
      st.visited.card ≤ st₀.visited.card + (script.filter Option.isSome).length := by
  induction script with
  | nil =>
    intro st₀ st h
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp
  | cons s ss ih =>
    intro st₀ st h
    rw [List.foldlM_cons] at h
    cases hstep : dfsStep H q d ports π st₀ s with
    | none => simp [hstep] at h
    | some st₁ =>
      simp only [hstep, Option.bind_some] at h
      have h1 := dfsStep_visited_card H q d ports π st₀ st₁ s hstep
      have h2 := ih st₁ st h
      cases s <;> simp at h1 ⊢ <;> omega

/-- Implicit discovered-vertex bound, p. 2: at most T+1 in any target fiber after ≤T queries. -/
theorem discoveredBound (H : FiniteGraph) (q d T : ℕ) (ports : PortTable H d)
    (π : Lift H q) (root : Fin H.n × Fin q) (script : List (DFSSymbol d))
    (st : DFSState H q) (run : dfsReplay H q d ports π root script = some st)
    (queries : (script.filter Option.isSome).length ≤ T) :
  st.visited.card ≤ T+1 ∧ ∀ v, (st.visited.filter fun x => x.1=v).card ≤ T+1 := by
  have h1 := foldlM_visited_card H q d ports π script ⟨[root], {root}, ∅, 0⟩ st run
  simp only [Finset.card_singleton] at h1
  have hcard : st.visited.card ≤ T + 1 := by omega
  refine ⟨hcard, fun v => le_trans (Finset.card_filter_le _ _) hcard⟩

end BuyAtBulk.EdgeOnlyGap
