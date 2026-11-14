import BuyAtBulk.EdgeOnlyGap.Helpers.ProofADFSAdaptiveState
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofADFSQueryTransition
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofAAdaptiveTranscript

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

/-- A successful query supplies its current vertex and incident port. -/
theorem dfsStep_query_port (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (π : Lift H q) (st st' : DFSState H q) (p : Fin d) (flag : Bool)
    (run : dfsStep H q d ports π st (some (p,flag)) = some st') :
    ∃ x xs e, st.stack = x::xs ∧ ports.port x.1 p = some e := by
  cases hs : st.stack with
  | nil => simp [dfsStep, hs] at run
  | cons x xs =>
    cases hp : ports.port x.1 p with
    | none => simp [dfsStep, hs, hp] at run
    | some e => exact ⟨x,xs,e,rfl,hp⟩

/-- The adaptive policy reproduces exactly the first k actual matching queries of a
successful replay, including all returns between consecutive queries. -/
theorem dfsReplay_transcript (H : FiniteGraph) (q d T : ℕ) (ports : PortTable H d)
    (π : Lift H q) (root : Fin H.n × Fin q) (script : List (DFSSymbol d))
    (final : DFSState H q) (run : dfsReplay H q d ports π root script = some final)
    (queries : (script.filter Option.isSome).length ≤ T) :
    ∀ k ≤ (script.filter Option.isSome).length,
      let hist := adaptiveTranscript H q T (historyPolicy H q d T ports root script) π k
      hist.length = k ∧ ∃ st,
        dfsReplay H q d ports π root (queryPrefix k script) = some st ∧
        st.queried = exposureKeys H q hist := by
  intro k
  induction k with
  | zero =>
    intro _
    obtain ⟨st,hst⟩ := dfsReplay_queryPrefix H q d ports π root script final run 0
    refine ⟨rfl,st,hst,?_⟩
    have hc := foldlM_queried_card H q d ports π (queryPrefix 0 script) _ st hst
    have hz : st.queried.card = 0 := by simpa [queryPrefix_queries] using hc
    simpa [adaptiveTranscript,exposureKeys] using Finset.card_eq_zero.mp hz
  | succ k ih =>
    intro hk
    obtain ⟨hlen,st,hst,hkeys⟩ := ih (by omega)
    let hist := adaptiveTranscript H q T (historyPolicy H q d T ports root script) π k
    have hl : hist.length = k := hlen
    have hc := transcript_consistent H q T (historyPolicy H q d T ports root script) π k
    obtain ⟨before,one,after,⟨p,flag⟩,ss,hbefore,hsuf,hstep,hafter,hqa,hva,hsa⟩ :=
      dfsReplay_queryTransition H q d ports π root script final run k (by omega)
    have heq : before = st := Option.some.inj (hbefore.symm.trans hst)
    subst before
    obtain ⟨x,xs,e,hstack,hport⟩ := dfsStep_query_port H q d ports π st one p flag hstep
    have hn := historyPolicy_next_of_step H q d T ports root script hist π st one hc
      (by simpa only [hl] using hst) hkeys x xs p flag ss e hstack hport
      (by simpa only [hl] using hsuf) hstep
    have hd := dfsStep_query_data H q d ports π st one x xs p flag e hstack hport hstep
    have ht : hist.length < T := by omega
    have hnext : adaptiveTranscript H q T (historyPolicy H q d T ports root script) π (k+1) =
        hist ++ [if decide (x.1 ≠ e.val.1) then (e,(π e).symm x.2,x.2)
          else (e,x.2,π e x.2)] := by
      change (if hist.length < T then _ else _) = _
      rw [if_pos ht,hn]
    refine ⟨?_,after,hafter,?_⟩
    · rw [hnext,List.length_append,List.length_singleton,hl]
    · rw [hqa,hd.2.2.1,hkeys,hnext]
      by_cases hx : x.1 = e.val.1 <;> simp [exposureKeys,hx,hist]

end BuyAtBulk.EdgeOnlyGap.ProofA
