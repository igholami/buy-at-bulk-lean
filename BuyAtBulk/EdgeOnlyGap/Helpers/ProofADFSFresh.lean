import BuyAtBulk.EdgeOnlyGap.Items.DFSEdges
import Mathlib.Tactic

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

 theorem dfsStep_queried_mono (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (π : Lift H q) (st₀ st₁ : DFSState H q) (s : DFSSymbol d)
    (h : dfsStep H q d ports π st₀ s = some st₁) : st₀.queried ⊆ st₁.queried := by
  unfold dfsStep at h
  cases hs : st₀.stack with
  | nil => simp [hs] at h
  | cons x xs =>
    rw [hs] at h
    cases s with
    | none =>
      dsimp at h
      split_ifs at h
      cases h
      exact Finset.Subset.refl _
    | some a =>
      rcases a with ⟨p,flag⟩
      dsimp at h
      cases hp : ports.port x.1 p with
      | none => simp [hp] at h
      | some e =>
        rw [hp] at h
        dsimp at h
        split_ifs at h
        all_goals cases h; exact Finset.subset_insert _ _

 theorem dfsStep_queried_card (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (π : Lift H q) (st₀ st₁ : DFSState H q) (s : DFSSymbol d)
    (h : dfsStep H q d ports π st₀ s = some st₁) :
    st₁.queried.card = st₀.queried.card + if s.isSome then 1 else 0 := by
  unfold dfsStep at h
  cases hs : st₀.stack with
  | nil => simp [hs] at h
  | cons x xs =>
    rw [hs] at h
    cases s with
    | none =>
      dsimp at h
      split_ifs at h
      cases h
      simp
    | some a =>
      rcases a with ⟨p,flag⟩
      dsimp at h
      cases hp : ports.port x.1 p with
      | none => simp [hp] at h
      | some e =>
        rw [hp] at h
        dsimp at h
        split_ifs at h
        all_goals cases h; simp_all

 theorem foldlM_queried_mono (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (π : Lift H q) (script : List (DFSSymbol d)) :
    ∀ st₀ st : DFSState H q,
      script.foldlM (dfsStep H q d ports π) st₀ = some st → st₀.queried ⊆ st.queried := by
  induction script with
  | nil => intro st₀ st h; cases Option.some.inj h; exact Finset.Subset.refl _
  | cons s ss ih =>
    intro st₀ st h
    rw [List.foldlM_cons] at h
    cases hs : dfsStep H q d ports π st₀ s with
    | none => simp [hs] at h
    | some st₁ =>
      simp only [hs, Option.bind_some] at h
      exact (dfsStep_queried_mono H q d ports π st₀ st₁ s hs).trans (ih st₁ st h)

 theorem foldlM_queried_card (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (π : Lift H q) (script : List (DFSSymbol d)) :
    ∀ st₀ st : DFSState H q,
      script.foldlM (dfsStep H q d ports π) st₀ = some st →
      st.queried.card = st₀.queried.card + (script.filter Option.isSome).length := by
  induction script with
  | nil => intro st₀ st h; cases Option.some.inj h; simp
  | cons s ss ih =>
    intro st₀ st h
    rw [List.foldlM_cons] at h
    cases hs : dfsStep H q d ports π st₀ s with
    | none => simp [hs] at h
    | some st₁ =>
      simp only [hs, Option.bind_some] at h
      have h1 := dfsStep_queried_card H q d ports π st₀ st₁ s hs
      have h2 := ih st₁ st h
      cases s <;> simp at h1 ⊢ <;> omega

/-- Only the fresh pair recorded by a successful step can affect that step. -/
 theorem dfsStep_agreement (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (π ρ : Lift H q) (st₀ st₁ : DFSState H q) (s : DFSSymbol d)
    (h : dfsStep H q d ports π st₀ s = some st₁)
    (agree : ∀ ej ∈ st₁.queried, ρ ej.1 ej.2 = π ej.1 ej.2) :
    dfsStep H q d ports ρ st₀ s = some st₁ := by
  cases hs : st₀.stack with
  | nil => simp [dfsStep, hs] at h
  | cons x xs =>
    cases s with
    | none => simpa only [dfsStep, hs] using h
    | some a =>
      rcases a with ⟨p,flag⟩
      cases hp : ports.port x.1 p with
      | none => simp [dfsStep, hs, hp] at h
      | some e =>
        by_cases hx : x.1 = e.val.1
        · have hmem : (e,x.2) ∈ st₁.queried := by
            simp only [dfsStep, hs, hp] at h
            simp only [hx, ↓reduceIte] at h
            split_ifs at h
            all_goals cases h; exact Finset.mem_insert_self _ _
          have ha := agree (e,x.2) hmem
          simp only [dfsStep, hs, hp] at h ⊢
          simpa only [hx, ↓reduceIte, ha] using h
        · have hmem : (e,(π e).symm x.2) ∈ st₁.queried := by
            simp only [dfsStep, hs, hp] at h
            simp only [hx, ↓reduceIte] at h
            split_ifs at h
            all_goals cases h; exact Finset.mem_insert_self _ _
          have ha := agree (e,(π e).symm x.2) hmem
          have hinv : (ρ e).symm x.2 = (π e).symm x.2 := by
            apply (Equiv.symm_apply_eq (ρ e)).mpr
            simpa using ha.symm
          simp only [dfsStep, hs, hp] at h ⊢
          simpa only [hx, ↓reduceIte, hinv] using h

/-- A completed replay is fixed by the matching pairs that it actually queried. -/
 theorem foldlM_agreement (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (π ρ : Lift H q) (script : List (DFSSymbol d)) :
    ∀ st₀ st : DFSState H q,
      script.foldlM (dfsStep H q d ports π) st₀ = some st →
      (∀ ej ∈ st.queried, ρ ej.1 ej.2 = π ej.1 ej.2) →
      script.foldlM (dfsStep H q d ports ρ) st₀ = some st := by
  induction script with
  | nil => intro st₀ st h _; exact h
  | cons s ss ih =>
    intro st₀ st h agree
    rw [List.foldlM_cons] at h ⊢
    cases hs : dfsStep H q d ports π st₀ s with
    | none => simp [hs] at h
    | some st₁ =>
      simp only [hs, Option.bind_some] at h
      have hsub := foldlM_queried_mono H q d ports π ss st₁ st h
      rw [dfsStep_agreement H q d ports π ρ st₀ st₁ s hs (fun ej he => agree ej (hsub he))]
      exact ih st₁ st h agree

 theorem dfsReplay_agreement (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (π ρ : Lift H q) (root : Fin H.n × Fin q) (script : List (DFSSymbol d))
    (st : DFSState H q) (run : dfsReplay H q d ports π root script = some st)
    (agree : ∀ ej ∈ st.queried, ρ ej.1 ej.2 = π ej.1 ej.2) :
    dfsReplay H q d ports ρ root script = some st :=
  foldlM_agreement H q d ports π ρ script _ st run agree

end BuyAtBulk.EdgeOnlyGap.ProofA
