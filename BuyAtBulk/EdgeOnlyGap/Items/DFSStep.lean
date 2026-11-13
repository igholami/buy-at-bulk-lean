import BuyAtBulk.EdgeOnlyGap.Items.DFSScript

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit precise script semantics, p. 2: expose each selected edge once; returns do not expose. -/
def dfsStep (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d) (π : Lift H q)
    (st : DFSState H q) (s : DFSSymbol d) : Option (DFSState H q) := by
  classical
  exact match st.stack with
  | [] => none
  | x::xs => match s with
    | none => if xs.isEmpty then none else some {st with stack := xs}
    | some (p,newFlag) => match ports.port x.1 p with
      | none => none
      | some e =>
        let j := if x.1=e.val.1 then x.2 else (π e).symm x.2
        let y := if x.1=e.val.1 then (e.val.2,π e j) else (e.val.1,j)
        if (e,j) ∈ st.queried then none else
        if newFlag = decide (y ∉ st.visited) then
          some {stack := if newFlag then y::st.stack else st.stack
                visited := insert y st.visited
                queried := insert (e,j) st.queried
                surplus := st.surplus + if newFlag then 0 else 1}
        else none

end BuyAtBulk.EdgeOnlyGap
