import BuyAtBulk.EdgeOnlyGap.Items.LiftAsFiniteGraph

import BuyAtBulk.EdgeOnlyGap.Items.DFSStep

import BuyAtBulk.EdgeOnlyGap.Items.DfsReplay

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 2: selected lifted edges of the replay, in finite lift coordinates. -/
def dfsEdges (H : FiniteGraph) (q : ℕ) (π : Lift H q) (st : DFSState H q) :
    Finset (Edges (lifted H q π)) := by
  classical
  let code := Fintype.equivFin (Fin H.n × Fin q)
  exact Finset.univ.filter fun a => ∃ ej ∈ st.queried,
    s(a.val.1,a.val.2) = s(finCongr (by simp [lifted]) (code (ej.1.val.1,ej.2)),
       finCongr (by simp [lifted]) (code (ej.1.val.2,π ej.1 ej.2)))

end BuyAtBulk.EdgeOnlyGap
