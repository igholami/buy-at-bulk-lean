import BuyAtBulk.EdgeOnlyGap.Helpers.ProofADFSQueryPrefix
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofADFSStepData

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

/-- Intervening return symbols neither reveal pairs nor change the discovered vertices. -/
theorem foldlM_returns (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (π : Lift H q) (script : List (DFSSymbol d)) (hqueries : (script.filter Option.isSome).length = 0) :
    ∀ st₀ st : DFSState H q,
      script.foldlM (dfsStep H q d ports π) st₀ = some st →
      st.queried = st₀.queried ∧ st.visited = st₀.visited ∧ st.surplus = st₀.surplus := by
  induction script with
  | nil => intro st₀ st h; cases Option.some.inj h; exact ⟨rfl,rfl,rfl⟩
  | cons s ss ih =>
    cases s with
    | some a => simp at hqueries
    | none =>
      have hss : (ss.filter Option.isSome).length = 0 := by simpa using hqueries
      intro st₀ st h
      rw [List.foldlM_cons] at h
      cases hs : dfsStep H q d ports π st₀ none with
      | none => simp [hs] at h
      | some st₁ =>
        simp only [hs, Option.bind_some] at h
        have hh := ih hss st₁ st h
        unfold dfsStep at hs
        cases ht : st₀.stack with
        | nil => simp [ht] at hs
        | cons x xs =>
          simp only [ht] at hs
          split_ifs at hs
          cases hs
          exact hh

/-- A successful script supplies the next actual fresh query and all following returns,
without treating returns as matching exposures. -/
theorem dfsReplay_queryTransition (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (π : Lift H q) (root : Fin H.n × Fin q) (script : List (DFSSymbol d))
    (final : DFSState H q) (run : dfsReplay H q d ports π root script = some final)
    (k : ℕ) (hk : k < (script.filter Option.isSome).length) :
    ∃ st st' after : DFSState H q, ∃ pflag : Fin d × Bool, ∃ ss : List (DFSSymbol d),
      dfsReplay H q d ports π root (queryPrefix k script) = some st ∧
      querySuffix k script = some pflag::ss ∧
      dfsStep H q d ports π st (some pflag) = some st' ∧
      dfsReplay H q d ports π root (queryPrefix (k+1) script) = some after ∧
      after.queried = st'.queried ∧ after.visited = st'.visited ∧ after.surplus = st'.surplus := by
  obtain ⟨st,hst⟩ := dfsReplay_queryPrefix H q d ports π root script final run k
  obtain ⟨after,hafter⟩ := dfsReplay_queryPrefix H q d ports π root script final run (k+1)
  obtain ⟨pflag,ss,hsuf⟩ := querySuffix_starts_query k script hk
  have ha := hafter
  rw [queryPrefix_step k script pflag ss hsuf] at ha
  unfold dfsReplay at ha hst
  rw [List.foldlM_append, hst] at ha
  simp only [Option.bind_some, List.foldlM_cons] at ha
  cases hstep : dfsStep H q d ports π st (some pflag) with
  | none => simp [hstep] at ha
  | some st' =>
    have ha' : (queryPrefix 0 ss).foldlM (dfsStep H q d ports π) st' = some after := by
      simpa [hstep] using ha
    have hret := foldlM_returns H q d ports π (queryPrefix 0 ss)
      (by simp [queryPrefix_queries]) st' after ha'
    exact ⟨st,st',after,pflag,ss,hst,hsuf,hstep,hafter,hret⟩

end BuyAtBulk.EdgeOnlyGap.ProofA
