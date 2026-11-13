import BuyAtBulk.EdgeOnlyGap.Items.DFSEdges
import Mathlib.Tactic

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

def surplusSymbol {d : ℕ} (s : DFSSymbol d) : Bool :=
  match s with | some (_,false) => true | _ => false

 theorem dfsStep_surplus (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (π : Lift H q) (st₀ st₁ : DFSState H q) (s : DFSSymbol d)
    (h : dfsStep H q d ports π st₀ s = some st₁) :
    st₁.surplus = st₀.surplus + if surplusSymbol s then 1 else 0 := by
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
      simp [surplusSymbol]
    | some a =>
      rcases a with ⟨p,flag⟩
      dsimp at h
      cases hp : ports.port x.1 p with
      | none => simp [hp] at h
      | some e =>
        rw [hp] at h
        dsimp at h
        split_ifs at h
        all_goals cases h; cases flag <;> simp_all [surplusSymbol]

 theorem foldlM_surplus (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (π : Lift H q) (script : List (DFSSymbol d)) :
    ∀ st₀ st : DFSState H q,
      script.foldlM (dfsStep H q d ports π) st₀ = some st →
      st.surplus = st₀.surplus + (script.filter surplusSymbol).length := by
  induction script with
  | nil =>
    intro st₀ st h
    have heq : st₀ = st := Option.some.inj h
    subst st
    simp
  | cons s ss ih =>
    intro st₀ st h
    rw [List.foldlM_cons] at h
    cases hs : dfsStep H q d ports π st₀ s with
    | none => simp [hs] at h
    | some st₁ =>
      simp only [hs, Option.bind_some] at h
      have h1 := dfsStep_surplus H q d ports π st₀ st₁ s hs
      have h2 := ih st₁ st h
      by_cases hf : surplusSymbol s <;> simp [hf] <;> simp [hf] at h1 <;> omega

 theorem dfsReplay_surplus (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (π : Lift H q) (root : Fin H.n × Fin q) (script : List (DFSSymbol d))
    (st : DFSState H q) (run : dfsReplay H q d ports π root script = some st) :
    st.surplus = (script.filter surplusSymbol).length := by
  simpa using foldlM_surplus H q d ports π script ⟨[root],{root},∅,0⟩ st run

end BuyAtBulk.EdgeOnlyGap.ProofA
