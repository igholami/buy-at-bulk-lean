import BuyAtBulk.EdgeOnlyGap.Items.DFSEdges
import Mathlib.Tactic

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

def discoverySymbol {d : ℕ} (s : DFSSymbol d) : Bool :=
  match s with | some (_,true) => true | _ => false

 theorem dfsStep_visited_card (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (π : Lift H q) (st₀ st₁ : DFSState H q) (s : DFSSymbol d)
    (h : dfsStep H q d ports π st₀ s = some st₁) :
    st₁.visited.card = st₀.visited.card + if discoverySymbol s then 1 else 0 := by
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
      simp [discoverySymbol]
    | some a =>
      rcases a with ⟨p,flag⟩
      dsimp at h
      cases hp : ports.port x.1 p with
      | none => simp [hp] at h
      | some e =>
        rw [hp] at h
        dsimp at h
        split_ifs at h
        all_goals cases h; cases flag <;> simp_all [discoverySymbol]

 theorem dfsStep_stack_length (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (π : Lift H q) (st₀ st₁ : DFSState H q) (s : DFSSymbol d)
    (h : dfsStep H q d ports π st₀ s = some st₁) :
    st₁.stack.length + (if s.isNone then 1 else 0) =
      st₀.stack.length + if discoverySymbol s then 1 else 0 := by
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
      simp [discoverySymbol, hs]
    | some a =>
      rcases a with ⟨p,flag⟩
      dsimp at h
      cases hp : ports.port x.1 p with
      | none => simp [hp] at h
      | some e =>
        rw [hp] at h
        dsimp at h
        split_ifs at h
        all_goals cases h; cases flag <;> simp_all [discoverySymbol]

 theorem foldlM_vertex_counts (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (π : Lift H q) (script : List (DFSSymbol d)) :
    ∀ st₀ st : DFSState H q,
      script.foldlM (dfsStep H q d ports π) st₀ = some st →
      st.visited.card = st₀.visited.card + (script.filter discoverySymbol).length ∧
      st.stack.length + (script.filter Option.isNone).length =
        st₀.stack.length + (script.filter discoverySymbol).length := by
  induction script with
  | nil => intro st₀ st h; cases Option.some.inj h; simp
  | cons s ss ih =>
    intro st₀ st h
    rw [List.foldlM_cons] at h
    cases hs : dfsStep H q d ports π st₀ s with
    | none => simp [hs] at h
    | some st₁ =>
      simp only [hs, Option.bind_some] at h
      have hv := dfsStep_visited_card H q d ports π st₀ st₁ s hs
      have hl := dfsStep_stack_length H q d ports π st₀ st₁ s hs
      have hh := ih st₁ st h
      cases s with
      | none => simp [List.filter_cons, discoverySymbol] at hv hl hh ⊢; omega
      | some a =>
        rcases a with ⟨p,flag⟩
        cases flag <;> simp [List.filter_cons, discoverySymbol] at hv hl hh ⊢ <;> omega

 theorem dfsReplay_vertex_counts (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (π : Lift H q) (root : Fin H.n × Fin q) (script : List (DFSSymbol d))
    (st : DFSState H q) (run : dfsReplay H q d ports π root script = some st) :
    st.visited.card = 1 + (script.filter discoverySymbol).length ∧
      st.stack.length + (script.filter Option.isNone).length =
        1 + (script.filter discoverySymbol).length := by
  simpa using foldlM_vertex_counts H q d ports π script ⟨[root],{root},∅,0⟩ st run

end BuyAtBulk.EdgeOnlyGap.ProofA
