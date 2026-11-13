import BuyAtBulk.EdgeOnlyGap.Helpers.ProofADFSSelectedStep

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

def saturated (H : FiniteGraph) (q : ℕ) (π : Lift H q)
    (allowed queried : Finset (Edges H × Fin q)) (x : Fin H.n × Fin q) : Prop :=
  ∀ ej ∈ allowed, keyIncident H q π ej x → ej ∈ queried

structure SearchInvariant (H : FiniteGraph) (q : ℕ) (π : Lift H q)
    (allowed : Finset (Edges H × Fin q)) (root : Fin H.n × Fin q) (st : DFSState H q) : Prop where
  tail : ∃ xs, st.stack = xs ++ [root]
  stackVisited : ∀ x ∈ st.stack, x ∈ st.visited
  selected : st.queried ⊆ allowed
  visitedSupport : st.visited ⊆ keySupport H q π allowed
  endpoints : ∀ ej ∈ st.queried, keyLeft H q ej ∈ st.visited ∧ keyRight H q π ej ∈ st.visited
  popped : ∀ x ∈ st.visited, x ∉ st.stack → saturated H q π allowed st.queried x

/-- Finite DFS termination. Only saturated vertices may be popped; every query
inserts a genuinely fresh selected key. -/
theorem dfsSearch (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d) (π : Lift H q)
    (allowed : Finset (Edges H × Fin q)) (root : Fin H.n × Fin q) :
    ∀ st : DFSState H q, SearchInvariant H q π allowed root st →
      ∃ (script : List (DFSSymbol d)) (final : DFSState H q), script.foldlM (dfsStep H q d ports π) st = some final ∧
        SearchInvariant H q π allowed root final ∧ final.stack = [root] ∧
        ∀ x ∈ final.visited, saturated H q π allowed final.queried x := by
  intro st
  induction hn : 2*(allowed.card-st.queried.card)+st.stack.length using Nat.strong_induction_on generalizing st with
  | h n ih =>
    intro inv
    obtain ⟨stem,hroot⟩ := inv.tail
    cases hs : st.stack with
    | nil => simp [hs] at hroot
    | cons x xs =>
      by_cases hsat : saturated H q π allowed st.queried x
      · cases xs with
        | nil =>
          have hx : x = root := by simpa [hs] using congrArg List.getLast? hroot
          refine ⟨[],st,rfl,inv,by simpa [hx] using hs,?_⟩
          intro y hy
          by_cases hyx : y = x
          · simpa [hyx] using hsat
          · exact inv.popped y hy (by simp [hs,hyx])
        | cons z zs =>
          let next : DFSState H q := {st with stack := z::zs}
          have hstep : dfsStep H q d ports π st none = some next := by simp [dfsStep,hs,next]
          have hinv : SearchInvariant H q π allowed root next := by
            refine ⟨?_,?_,inv.selected,inv.visitedSupport,inv.endpoints,?_⟩
            · cases stem with
              | nil => simp [hs] at hroot
              | cons a as =>
                refine ⟨as,?_⟩
                exact (List.cons.inj (hs.symm.trans hroot)).2
            · intro y hy
              exact inv.stackVisited y (by rw [hs]; exact List.mem_cons_of_mem x hy)
            · intro y hy hys
              by_cases hyx : y = x
              · simpa [hyx] using hsat
              · exact inv.popped y hy (by simpa [hs,hyx,next] using hys)
          have hlt : 2*(allowed.card-next.queried.card)+next.stack.length < n := by
            simp only [next,hs,List.length_cons] at hn ⊢
            omega
          obtain ⟨script,final,hr,hi,hf,hclose⟩ := ih _ hlt next rfl hinv
          refine ⟨none::script,final,?_,hi,hf,hclose⟩
          simpa [List.foldlM_cons,hstep] using hr
      · obtain ⟨ej,he,hincident,hfresh⟩ : ∃ ej ∈ allowed, keyIncident H q π ej x ∧ ej ∉ st.queried := by
          simpa [saturated,not_forall,not_imp,and_assoc] using hsat
        obtain ⟨p,flag,y,hy,hstep,hflag,hleft,hright⟩ :=
          dfsStep_selected H q d ports π st x xs ej hs hincident hfresh
        let next : DFSState H q :=
          {stack := if flag then y::st.stack else st.stack
           visited := insert y st.visited
           queried := insert ej st.queried
           surplus := st.surplus + if flag then 0 else 1}
        have hnext : dfsStep H q d ports π st (some (p,flag)) = some next := hstep
        have hySupport := keySupport_mem H q π allowed ej he y hy
        have hxVisited := inv.stackVisited x (by simp [hs])
        have hinv : SearchInvariant H q π allowed root next := by
          refine ⟨?_,?_,?_,?_,?_,?_⟩
          · cases flag with
            | false => exact inv.tail
            | true => exact ⟨y::stem,by simp [next,hroot]⟩
          · intro a ha
            cases flag <;> simp only [next,Bool.false_eq_true,↓reduceIte,List.mem_cons] at ha
            · exact Finset.mem_insert_of_mem (inv.stackVisited a ha)
            · rcases ha with rfl | ha
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (inv.stackVisited a ha)
          · exact Finset.insert_subset he inv.selected
          · exact Finset.insert_subset hySupport inv.visitedSupport
          · intro key hk
            rcases Finset.mem_insert.mp hk with rfl | hk
            · constructor
              · rcases hleft with hl | hl <;> rw [hl]
                · exact Finset.mem_insert_of_mem hxVisited
                · exact Finset.mem_insert_self _ _
              · rcases hright with hr | hr <;> rw [hr]
                · exact Finset.mem_insert_of_mem hxVisited
                · exact Finset.mem_insert_self _ _
            · exact ⟨Finset.mem_insert_of_mem (inv.endpoints key hk).1,
                Finset.mem_insert_of_mem (inv.endpoints key hk).2⟩
          · intro a ha hstack
            have hold : a ∈ st.visited := by
              rcases Finset.mem_insert.mp ha with hay | ha
              · cases hf : flag with
                | false =>
                  have hv : y ∈ st.visited := by simpa [hf] using hflag.symm
                  exact hay.symm ▸ hv
                | true => simp [next,hf,hay] at hstack
              · exact ha
            have hnstack : a ∉ st.stack := by
              intro hm
              apply hstack
              cases flag <;> simp [next,hm]
            exact fun key hk hki => Finset.mem_insert_of_mem (inv.popped a hold hnstack key hk hki)
        have hcard : st.queried.card < allowed.card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨inv.selected,by
            intro heq; exact hfresh (heq.symm ▸ he)⟩)
        have hlt : 2*(allowed.card-next.queried.card)+next.stack.length < n := by
          have hc : next.queried.card = st.queried.card+1 := by simp [next,hfresh]
          have hl : next.stack.length ≤ st.stack.length+1 := by cases flag <;> simp [next]
          omega
        obtain ⟨script,final,hr,hi,hf,hclose⟩ := ih _ hlt next rfl hinv
        refine ⟨some (p,flag)::script,final,?_,hi,hf,hclose⟩
        simpa [List.foldlM_cons,hnext] using hr

end BuyAtBulk.EdgeOnlyGap.ProofA
