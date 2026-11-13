import BuyAtBulk.EdgeOnlyGap.Helpers.ProofADFSTranscript
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofAAdaptiveHit

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

/-- A prescribed false discovery flag in a successful replay is an actual adaptive
hit on coordinates of vertices discovered before that query. -/
theorem dfsReplay_false_hit (H : FiniteGraph) (q d T : ℕ) (ports : PortTable H d)
    (π : Lift H q) (root : Fin H.n × Fin q) (script : List (DFSSymbol d))
    (final : DFSState H q) (run : dfsReplay H q d ports π root script = some final)
    (queries : (script.filter Option.isSome).length ≤ T)
    (k : ℕ) (hk : k < (script.filter Option.isSome).length)
    (p : Fin d) (ss : List (DFSSymbol d))
    (hsuffix : querySuffix k script = some (p,false)::ss) :
    adaptiveHit H q T (historyPolicy H q d T ports root script)
      (historyOld H q d T ports root script) k π := by
  obtain ⟨hlen,st,hst,hkeys⟩ := dfsReplay_transcript H q d T ports π root script final run queries k (by omega)
  let hist := adaptiveTranscript H q T (historyPolicy H q d T ports root script) π k
  have hl : hist.length = k := hlen
  have hc := transcript_consistent H q T (historyPolicy H q d T ports root script) π k
  obtain ⟨before,one,after,⟨p',flag⟩,ss',hbefore,hsuf,hstep,hafter,hqa,hva,hsa⟩ :=
    dfsReplay_queryTransition H q d ports π root script final run k hk
  have heq : before = st := Option.some.inj (hbefore.symm.trans hst)
  subst before
  rw [hsuffix] at hsuf
  have hpairs := List.cons.inj hsuf
  have hpf := Option.some.inj hpairs.1
  have hpeq : p = p' := congrArg Prod.fst hpf
  have hflag : false = flag := congrArg Prod.snd hpf
  subst p'
  subst flag
  obtain ⟨x,xs,e,hstack,hport⟩ := dfsStep_query_port H q d ports π st one p false hstep
  have hn := historyPolicy_next_of_step H q d T ports root script hist π st one hc
    (by simpa only [hl] using hst) hkeys x xs p false ss e hstack hport
    (by simpa only [hl] using hsuffix) hstep
  have hs := historyState_of_run H q d ports root script hist π st hc
    (by simpa only [hl] using hst) hkeys
  have hd := dfsStep_query_data H q d ports π st one x xs p false e hstack hport hstep
  change ∃ e rev j, _
  refine ⟨e,decide (x.1 ≠ e.val.1),x.2,by omega,hn,?_⟩
  by_cases hx : x.1 = e.val.1
  · have hy : (e.val.2,π e x.2) ∈ st.visited := by
      have hf := hd.2.1
      simpa [hx] using hf.symm
    have hm := historyOld_mem H q d T ports root script hist st hs (by omega)
      (e.val.2,π e x.2) hy
    simpa [hx] using hm
  · have hy : (e.val.1,(π e).symm x.2) ∈ st.visited := by
      have hf := hd.2.1
      simpa [hx] using hf.symm
    have hm := historyOld_mem H q d T ports root script hist st hs (by omega)
      (e.val.1,(π e).symm x.2) hy
    simpa [hx] using hm

end BuyAtBulk.EdgeOnlyGap.ProofA
