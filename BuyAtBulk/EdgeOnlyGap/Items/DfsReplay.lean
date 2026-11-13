import BuyAtBulk.EdgeOnlyGap.Items.DFSStep

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit full script replay, p. 2. -/
def dfsReplay (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d) (π : Lift H q)
    (root : Fin H.n × Fin q) (script : List (DFSSymbol d)) : Option (DFSState H q) :=
  script.foldlM (dfsStep H q d ports π) ⟨[root],{root},∅,0⟩

end BuyAtBulk.EdgeOnlyGap
