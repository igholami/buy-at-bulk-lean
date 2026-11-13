import BuyAtBulk.EdgeOnlyGap.Helpers.ProofADFSHistory

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

/-- Exact successful-step data, including the fresh key and the discovery test. -/
theorem dfsStep_query_data (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (π : Lift H q) (st st' : DFSState H q) (x : Fin H.n × Fin q)
    (xs : List (Fin H.n × Fin q)) (p : Fin d) (flag : Bool) (e : Edges H)
    (hstack : st.stack = x::xs) (hport : ports.port x.1 p = some e)
    (run : dfsStep H q d ports π st (some (p,flag)) = some st') :
    let j := if x.1=e.val.1 then x.2 else (π e).symm x.2
    let y := if x.1=e.val.1 then (e.val.2,π e j) else (e.val.1,j)
    (e,j) ∉ st.queried ∧ flag = decide (y ∉ st.visited) ∧
      st'.queried = insert (e,j) st.queried ∧ st'.visited = insert y st.visited ∧
      st'.stack = (if flag then y::st.stack else st.stack) ∧
      st'.surplus = st.surplus + if flag then 0 else 1 := by
  have hfresh := dfsStep_query_fresh H q d ports π st st' x xs p flag e hstack hport run
  simp only [dfsStep, hstack, hport] at run
  dsimp only
  by_cases hx : x.1=e.val.1
  · simp only [hx, ↓reduceIte] at run hfresh ⊢
    split_ifs at run
    all_goals cases run; simp_all
  · simp only [hx, ↓reduceIte] at run hfresh ⊢
    split_ifs at run
    all_goals cases run; simp_all

end BuyAtBulk.EdgeOnlyGap.ProofA
