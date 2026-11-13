import BuyAtBulk.EdgeOnlyGap.Helpers.ProofADFSStepData
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofALiftEdgeKeys

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

def keyLeft (H : FiniteGraph) (q : ℕ) (ej : Edges H × Fin q) : Fin H.n × Fin q :=
  (ej.1.val.1,ej.2)
def keyRight (H : FiniteGraph) (q : ℕ) (π : Lift H q) (ej : Edges H × Fin q) : Fin H.n × Fin q :=
  (ej.1.val.2,π ej.1 ej.2)
def keyIncident (H : FiniteGraph) (q : ℕ) (π : Lift H q)
    (ej : Edges H × Fin q) (x : Fin H.n × Fin q) : Prop :=
  x = keyLeft H q ej ∨ x = keyRight H q π ej

def keySupport (H : FiniteGraph) (q : ℕ) (π : Lift H q)
    (allowed : Finset (Edges H × Fin q)) : Finset (Fin H.n × Fin q) :=
  allowed.biUnion fun ej => {keyLeft H q ej,keyRight H q π ej}

theorem keySupport_mem (H : FiniteGraph) (q : ℕ) (π : Lift H q)
    (allowed : Finset (Edges H × Fin q)) (ej : Edges H × Fin q) (he : ej ∈ allowed)
    (x : Fin H.n × Fin q) (hx : keyIncident H q π ej x) : x ∈ keySupport H q π allowed := by
  apply Finset.mem_biUnion.mpr
  exact ⟨ej,he,by simpa [keyIncident] using hx⟩

/-- Either endpoint of a fresh selected key supplies a genuine port query. -/
theorem dfsStep_selected (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (π : Lift H q) (st : DFSState H q) (x : Fin H.n × Fin q) (xs : List (Fin H.n × Fin q))
    (ej : Edges H × Fin q) (hstack : st.stack = x::xs)
    (hincident : keyIncident H q π ej x) (hfresh : ej ∉ st.queried) :
    ∃ p flag y, keyIncident H q π ej y ∧
      dfsStep H q d ports π st (some (p,flag)) = some
        { stack := if flag then y::st.stack else st.stack
          visited := insert y st.visited
          queried := insert ej st.queried
          surplus := st.surplus + if flag then 0 else 1 } ∧
      flag = decide (y ∉ st.visited) ∧
      (keyLeft H q ej = x ∨ keyLeft H q ej = y) ∧
      (keyRight H q π ej = x ∨ keyRight H q π ej = y) := by
  rcases ej with ⟨e,j⟩
  rcases hincident with hx | hx
  · subst x
    obtain ⟨p,hp⟩ := ports.complete e.val.1 e (Or.inl rfl)
    refine ⟨p,decide ((e.val.2,π e j) ∉ st.visited),(e.val.2,π e j),Or.inr rfl,?_,rfl,Or.inl rfl,Or.inr rfl⟩
    simp only [dfsStep,hstack,keyLeft,hp,↓reduceIte]
    simp [hfresh]
  · subst x
    obtain ⟨p,hp⟩ := ports.complete e.val.2 e (Or.inr rfl)
    have hne : e.val.2 ≠ e.val.1 := ne_of_gt e.prop.1
    refine ⟨p,decide ((e.val.1,j) ∉ st.visited),(e.val.1,j),Or.inl rfl,?_,rfl,Or.inr rfl,Or.inl rfl⟩
    simp only [dfsStep,hstack,keyRight,hp]
    simp [hne,hfresh]

end BuyAtBulk.EdgeOnlyGap.ProofA
