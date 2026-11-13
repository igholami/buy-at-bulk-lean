import BuyAtBulk.EdgeOnlyGap.Helpers.ProofADFSFresh
import BuyAtBulk.EdgeOnlyGap.Items.Exposure

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

/-- Matching-edge source keys represented by an exposure history. -/
def exposureKeys (H : FiniteGraph) (q : ℕ) (hist : List (Exposure H q)) :
    Finset (Edges H × Fin q) :=
  (hist.map fun a => (a.1,a.2.1)).toFinset

 theorem dfsStep_query_fresh (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (π : Lift H q) (st st' : DFSState H q) (x : Fin H.n × Fin q)
    (xs : List (Fin H.n × Fin q)) (p : Fin d) (flag : Bool) (e : Edges H)
    (hstack : st.stack = x::xs) (hport : ports.port x.1 p = some e)
    (run : dfsStep H q d ports π st (some (p,flag)) = some st') :
    (e,if x.1=e.val.1 then x.2 else (π e).symm x.2) ∉ st.queried := by
  intro hm
  simp only [dfsStep, hstack, hport] at run
  simp only [hm, ↓reduceIte, reduceCtorEq] at run

/-- Successful forward/reverse steps are fresh in the actual conditioned matching,
not merely fresh in a graph exploration that ignores old matching exposures. -/
 theorem dfsStep_history_fresh (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (π : Lift H q) (hist : List (Exposure H q)) (st st' : DFSState H q)
    (x : Fin H.n × Fin q) (xs : List (Fin H.n × Fin q))
    (p : Fin d) (flag : Bool) (e : Edges H)
    (consistent : exposureEvent H q hist π) (keys : st.queried = exposureKeys H q hist)
    (hstack : st.stack = x::xs) (hport : ports.port x.1 p = some e)
    (run : dfsStep H q d ports π st (some (p,flag)) = some st') :
    if x.1=e.val.1 then x.2 ∉ exposedSources H q hist e
      else x.2 ∉ exposedTargets H q hist e := by
  have hfresh := dfsStep_query_fresh H q d ports π st st' x xs p flag e hstack hport run
  rw [keys] at hfresh
  by_cases hx : x.1=e.val.1
  · simp only [hx, ↓reduceIte] at hfresh ⊢
    intro hm
    simp only [exposedSources, List.mem_toFinset, List.mem_map, List.mem_filter,
      decide_eq_true_eq] at hm
    obtain ⟨a,⟨ha,he⟩,hj⟩ := hm
    apply hfresh
    simp only [exposureKeys, List.mem_toFinset, List.mem_map]
    exact ⟨a,ha,Prod.ext he hj⟩
  · simp only [hx, ↓reduceIte] at hfresh ⊢
    intro hm
    simp only [exposedTargets, List.mem_toFinset, List.mem_map, List.mem_filter,
      decide_eq_true_eq] at hm
    obtain ⟨a,⟨ha,he⟩,hk⟩ := hm
    have hpair := consistent a ha
    rw [he, hk] at hpair
    have hj : a.2.1 = (π e).symm x.2 := (Equiv.eq_symm_apply (π e)).mpr hpair
    apply hfresh
    simp only [exposureKeys, List.mem_toFinset, List.mem_map]
    exact ⟨a,ha,Prod.ext he hj⟩

/-- Two lifts agreeing with a replay's exact exposure history have the same replay result. -/
 theorem dfsReplay_history_agreement (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d)
    (π ρ : Lift H q) (hist : List (Exposure H q)) (root : Fin H.n × Fin q)
    (script : List (DFSSymbol d)) (st : DFSState H q)
    (run : dfsReplay H q d ports π root script = some st)
    (keys : st.queried = exposureKeys H q hist)
    (hπ : exposureEvent H q hist π) (hρ : exposureEvent H q hist ρ) :
    dfsReplay H q d ports ρ root script = some st := by
  apply dfsReplay_agreement H q d ports π ρ root script st run
  intro ej hej
  rw [keys] at hej
  simp only [exposureKeys, List.mem_toFinset, List.mem_map] at hej
  obtain ⟨a,ha,rfl⟩ := hej
  exact (hρ a ha).trans (hπ a ha).symm

end BuyAtBulk.EdgeOnlyGap.ProofA
