import BuyAtBulk.EdgeOnlyGap.Helpers.ProofADFSHistory
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofADFSQueryPrefix
import BuyAtBulk.EdgeOnlyGap.Items.DiscoveredBound
import BuyAtBulk.EdgeOnlyGap.Items.AdaptivePolicy

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

/-- A replay prefix explained by exactly the matching pairs in the given history. -/
structure DFSHistoryWitness (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (root : Fin H.n × Fin q) (script : List (DFSSymbol d)) (hist : List (Exposure H q)) where
  lift : Lift H q
  state : DFSState H q
  consistent : exposureEvent H q hist lift
  run : dfsReplay H q d ports lift root (queryPrefix hist.length script) = some state
  keys : state.queried = exposureKeys H q hist

/-- The replay state is reconstructed from prior information only. -/
def historyState (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (root : Fin H.n × Fin q) (script : List (DFSSymbol d)) (hist : List (Exposure H q)) :
    Option (DFSState H q) :=
  if h : Nonempty (DFSHistoryWitness H q d ports root script hist) then
    some (Classical.choice h).state else none

 theorem historyState_run (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (root : Fin H.n × Fin q) (script : List (DFSSymbol d)) (hist : List (Exposure H q))
    (st : DFSState H q) (hs : historyState H q d ports root script hist = some st)
    (π : Lift H q) (hπ : exposureEvent H q hist π) :
    dfsReplay H q d ports π root (queryPrefix hist.length script) = some st ∧
      st.queried = exposureKeys H q hist := by
  unfold historyState at hs
  split at hs
  · rename_i h
    cases Option.some.inj hs
    let w := Classical.choice h
    exact ⟨dfsReplay_history_agreement H q d ports w.lift π hist root _ w.state
      w.run w.keys w.consistent hπ, w.keys⟩
  · simp at hs

 theorem historyState_of_run (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (root : Fin H.n × Fin q) (script : List (DFSSymbol d)) (hist : List (Exposure H q))
    (π : Lift H q) (st : DFSState H q) (hπ : exposureEvent H q hist π)
    (run : dfsReplay H q d ports π root (queryPrefix hist.length script) = some st)
    (keys : st.queried = exposureKeys H q hist) :
    historyState H q d ports root script hist = some st := by
  have hw : Nonempty (DFSHistoryWitness H q d ports root script hist) :=
    ⟨⟨π,st,hπ,run,keys⟩⟩
  unfold historyState
  rw [dif_pos hw]
  let w := Classical.choice hw
  have hr := dfsReplay_history_agreement H q d ports w.lift π hist root _ w.state
    w.run w.keys w.consistent hπ
  rw [run] at hr
  exact hr.symm

 theorem historyState_visited (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (root : Fin H.n × Fin q) (script : List (DFSSymbol d)) (hist : List (Exposure H q))
    (st : DFSState H q) (hs : historyState H q d ports root script hist = some st) :
    st.visited.card ≤ hist.length+1 := by
  unfold historyState at hs
  split at hs
  · rename_i h
    cases Option.some.inj hs
    let w := Classical.choice h
    exact (discoveredBound H q d hist.length ports w.lift root _ w.state w.run
      (by rw [queryPrefix_queries]; exact Nat.min_le_left _ _)).1
  · simp at hs

/-- The coordinate targets used for an old-vertex hit; malformed/oversized histories stop. -/
def historyOld (H : FiniteGraph) (q d T : ℕ) (ports : PortTable H d)
    (root : Fin H.n × Fin q) (script : List (DFSSymbol d)) (hist : List (Exposure H q)) :
    Finset (Fin q) :=
  if hist.length ≤ T then
    match historyState H q d ports root script hist with
    | none => ∅
    | some st => st.visited.image Prod.snd
  else ∅

 theorem historyOld_small (H : FiniteGraph) (q d T : ℕ) (ports : PortTable H d)
    (root : Fin H.n × Fin q) (script : List (DFSSymbol d)) (hist : List (Exposure H q)) :
    (historyOld H q d T ports root script hist).card ≤ T+1 := by
  unfold historyOld
  split
  · rename_i hlen
    cases hs : historyState H q d ports root script hist with
    | none => simp
    | some st =>
      exact (Finset.card_image_le).trans ((historyState_visited H q d ports root script hist st hs).trans
        (Nat.add_le_add_right hlen 1))
  · simp

/-- The next query is read from the fixed script and the reconstructed prior state. -/
def historyQuery (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (root : Fin H.n × Fin q) (script : List (DFSSymbol d)) (hist : List (Exposure H q)) :
    Option (Edges H × Bool × Fin q) := do
  let st ← historyState H q d ports root script hist
  let some (p,_) ← (querySuffix hist.length script).head? | none
  let x ← st.stack.head?
  let e ← ports.port x.1 p
  pure (e,decide (x.1 ≠ e.val.1),x.2)

/-- Freshness is checked on the true exposed source/target sets, including reverse queries. -/
def historyPolicy (H : FiniteGraph) (q d T : ℕ) (ports : PortTable H d)
    (root : Fin H.n × Fin q) (script : List (DFSSymbol d)) : AdaptivePolicy H q T where
  next := fun hist => (historyQuery H q d ports root script hist).filter fun a =>
    decide (if a.2.1 then a.2.2 ∉ exposedTargets H q hist a.1
      else a.2.2 ∉ exposedSources H q hist a.1)
  fresh := by
    intro hist e rev j _ hn
    have hf := Option.filter_eq_some_iff.mp hn
    simpa using hf.2

 theorem historyPolicy_next_of_step (H : FiniteGraph) (q d T : ℕ) (ports : PortTable H d)
    (root : Fin H.n × Fin q) (script : List (DFSSymbol d)) (hist : List (Exposure H q))
    (π : Lift H q) (st st' : DFSState H q) (hπ : exposureEvent H q hist π)
    (run : dfsReplay H q d ports π root (queryPrefix hist.length script) = some st)
    (keys : st.queried = exposureKeys H q hist)
    (x : Fin H.n × Fin q) (xs : List (Fin H.n × Fin q)) (p : Fin d) (flag : Bool)
    (ss : List (DFSSymbol d)) (e : Edges H)
    (hstack : st.stack = x::xs) (hport : ports.port x.1 p = some e)
    (hsuffix : querySuffix hist.length script = some (p,flag)::ss)
    (step : dfsStep H q d ports π st (some (p,flag)) = some st') :
    (historyPolicy H q d T ports root script).next hist =
      some (e,decide (x.1 ≠ e.val.1),x.2) := by
  have hstate := historyState_of_run H q d ports root script hist π st hπ run keys
  have hfresh := dfsStep_history_fresh H q d ports π hist st st' x xs p flag e
    hπ keys hstack hport step
  have hquery : historyQuery H q d ports root script hist =
      some (e,decide (x.1 ≠ e.val.1),x.2) := by
    simp [historyQuery, hstate, hsuffix, hstack, hport]
  change (historyQuery H q d ports root script hist).filter _ = _
  rw [hquery]
  by_cases hx : x.1 = e.val.1
  · simp only [hx, ↓reduceIte] at hfresh
    simp [hx, hfresh]
  · simp only [hx, ↓reduceIte] at hfresh
    simp [hx, hfresh]

 theorem historyOld_mem (H : FiniteGraph) (q d T : ℕ) (ports : PortTable H d)
    (root : Fin H.n × Fin q) (script : List (DFSSymbol d)) (hist : List (Exposure H q))
    (st : DFSState H q) (hs : historyState H q d ports root script hist = some st)
    (hlen : hist.length ≤ T) (y : Fin H.n × Fin q) (hy : y ∈ st.visited) :
    y.2 ∈ historyOld H q d T ports root script hist := by
  simp only [historyOld, if_pos hlen, hs]
  exact Finset.mem_image.mpr ⟨y,hy,rfl⟩

end BuyAtBulk.EdgeOnlyGap.ProofA
