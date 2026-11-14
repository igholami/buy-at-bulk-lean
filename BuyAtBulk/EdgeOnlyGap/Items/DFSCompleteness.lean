import BuyAtBulk.EdgeOnlyGap.Items.DFSEdges
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofADFSCompleteSearch
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofADFSVertices
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofADFSCounts
import BuyAtBulk.EdgeOnlyGap.Items.CycleRankFormula

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 2: every rooted connected m-edge witness has an m-query DFS script with ≤m returns. -/
theorem dfsCompleteness (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d) (π : Lift H q)
    (W : Finset (Edges (lifted H q π))) (connected : edgeComponents (lifted H q π) W = 1)
    (root : Fin H.n × Fin q)
    (root_mem : finCongr (by simp [lifted]) (Fintype.equivFin (Fin H.n × Fin q) root) ∈
      edgeSupport (lifted H q π) W) :
  ∃ script : List (DFSSymbol d), ∃ st : DFSState H q,
    dfsReplay H q d ports π root script = some st ∧ st.stack = [root] ∧
    dfsEdges H q π st = W ∧
    (script.filter Option.isSome).length = W.card ∧
    (script.filter Option.isNone).length ≤ W.card ∧
    script.length ≤ 2*W.card ∧ st.surplus = beta (lifted H q π) W := by
  obtain ⟨script,st,run,hstack,hedges,hvertices⟩ :=
    ProofA.dfsCompleteSearch H q d ports π W connected root root_mem
  have hqueries : (script.filter Option.isSome).length = W.card := by
    have hc := ProofA.foldlM_queried_card H q d ports π script ⟨[root],{root},∅,0⟩ st run
    have he := ProofA.dfsEdges_card H q π st
    rw [hedges] at he
    simpa using hc.symm.trans he.symm
  have hv := ProofA.dfsReplay_vertex_counts H q d ports π root script st run
  have hs := ProofA.dfsReplay_surplus H q d ports π root script st run
  have hcounts : (script.filter Option.isSome).length =
        (script.filter ProofA.discoverySymbol).length + (script.filter ProofA.surplusSymbol).length ∧
      script.length = (script.filter Option.isSome).length + (script.filter Option.isNone).length := by
    have counts : ∀ ls : List (DFSSymbol d),
        (ls.filter Option.isSome).length =
          (ls.filter ProofA.discoverySymbol).length + (ls.filter ProofA.surplusSymbol).length ∧
        ls.length = (ls.filter Option.isSome).length + (ls.filter Option.isNone).length := by
      intro ls
      induction ls with
      | nil => simp
      | cons s ss ih =>
        cases s with
        | none => simp [ProofA.discoverySymbol,ProofA.surplusSymbol,List.filter_cons] at ih ⊢; omega
        | some a =>
          rcases a with ⟨p,flag⟩
          cases flag <;> simp [ProofA.discoverySymbol,ProofA.surplusSymbol,List.filter_cons] at ih ⊢ <;> omega
    exact counts script
  have hreturns : (script.filter Option.isNone).length ≤ W.card := by
    simp only [hstack,List.length_singleton] at hv
    omega
  refine ⟨script,st,run,hstack,hedges,hqueries,hreturns,by omega,?_⟩
  have hrank := (cycleRankFormula (lifted H q π) W).2
  rw [connected] at hrank
  rw [hs]
  omega

end BuyAtBulk.EdgeOnlyGap
