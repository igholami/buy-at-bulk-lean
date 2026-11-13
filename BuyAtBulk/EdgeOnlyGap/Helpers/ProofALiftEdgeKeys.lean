import BuyAtBulk.EdgeOnlyGap.Items.DFSEdges
import BuyAtBulk.EdgeOnlyGap.Items.LiftCovering
import Mathlib.Tactic

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

 def liftCode (H : FiniteGraph) (q : ℕ) (π : Lift H q) :
    (Fin H.n × Fin q) ≃ Fin (lifted H q π).n :=
  (Fintype.equivFin (Fin H.n × Fin q)).trans (finCongr (by simp [lifted]))

 theorem liftCode_adj (H : FiniteGraph) (q : ℕ) (π : Lift H q)
    (x y : Fin H.n × Fin q) :
    (lifted H q π).graph.Adj (liftCode H q π x) (liftCode H q π y) ↔
      (liftGraph H q π).Adj x y := by
  change (liftGraph H q π).Adj
    ((liftCode H q π).symm (liftCode H q π x))
    ((liftCode H q π).symm (liftCode H q π y)) ↔ _
  simp only [Equiv.symm_apply_apply]

 theorem edgeOfAdj_exists (G : FiniteGraph) {u v : Fin G.n}
    (h : G.graph.Adj u v) : ∃ e : Edges G, s(e.val.1,e.val.2) = s(u,v) := by
  rcases lt_or_gt_of_ne h.ne with hlt | hgt
  · exact ⟨⟨(u,v),hlt,h⟩,rfl⟩
  · exact ⟨⟨(v,u),hgt,h.symm⟩,Sym2.eq_swap⟩

 def edgeOfAdj (G : FiniteGraph) {u v : Fin G.n} (h : G.graph.Adj u v) : Edges G :=
  Classical.choose (edgeOfAdj_exists G h)

 theorem edgeOfAdj_sym2 (G : FiniteGraph) {u v : Fin G.n} (h : G.graph.Adj u v) :
    s((edgeOfAdj G h).val.1,(edgeOfAdj G h).val.2) = s(u,v) :=
  Classical.choose_spec (edgeOfAdj_exists G h)

 def liftKeyEdge (H : FiniteGraph) (q : ℕ) (π : Lift H q) (ej : Edges H × Fin q) :
    Edges (lifted H q π) :=
  edgeOfAdj (lifted H q π) ((liftCode_adj H q π _ _).mpr
    (((liftCovering H q π).2.2.2 ej.1 ej.2 (π ej.1 ej.2)).mpr rfl))

 theorem liftKeyEdge_sym2 (H : FiniteGraph) (q : ℕ) (π : Lift H q) (ej : Edges H × Fin q) :
    s((liftKeyEdge H q π ej).val.1,(liftKeyEdge H q π ej).val.2) =
      s(liftCode H q π (ej.1.val.1,ej.2),liftCode H q π (ej.1.val.2,π ej.1 ej.2)) :=
  edgeOfAdj_sym2 _ _

 theorem liftKeyEdge_injective (H : FiniteGraph) (q : ℕ) (π : Lift H q) :
    Function.Injective (liftKeyEdge H q π) := by
  intro a b hab
  have heq := congrArg (fun e : Edges (lifted H q π) => s(e.val.1,e.val.2)) hab
  rw [liftKeyEdge_sym2, liftKeyEdge_sym2] at heq
  rcases Sym2.eq_iff.mp heq with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · have h1' := (liftCode H q π).injective h1
    have h2' := (liftCode H q π).injective h2
    apply Prod.ext
    · exact Subtype.ext (Prod.ext (congrArg (fun x : Fin H.n × Fin q => x.1) h1') (congrArg (fun x : Fin H.n × Fin q => x.1) h2'))
    · exact congrArg (fun x : Fin H.n × Fin q => x.2) h1'
  · have h1' := congrArg (fun x : Fin H.n × Fin q => x.1) ((liftCode H q π).injective h1)
    have h2' := congrArg (fun x : Fin H.n × Fin q => x.1) ((liftCode H q π).injective h2)
    have ha := a.1.prop.1
    have hb := b.1.prop.1
    change a.1.val.1 = b.1.val.2 at h1'
    change a.1.val.2 = b.1.val.1 at h2'
    rw [h1',h2'] at ha
    exact False.elim (lt_asymm ha hb)

 theorem liftKeyEdge_bijective (H : FiniteGraph) (q : ℕ) (π : Lift H q) :
    Function.Bijective (liftKeyEdge H q π) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨liftKeyEdge_injective H q π, ?_⟩
  have h := (liftCovering H q π).2.1
  change Fintype.card (Edges (lifted H q π)) = q * Fintype.card (Edges H) at h
  simp only [Fintype.card_prod, Fintype.card_fin]
  exact (Nat.mul_comm _ _).trans h.symm

/-- The queried source keys represent exactly the selected lifted edges, without duplicates. -/
 theorem dfsEdges_image (H : FiniteGraph) (q : ℕ) (π : Lift H q) (st : DFSState H q) :
    dfsEdges H q π st = st.queried.image (liftKeyEdge H q π) := by
  apply Finset.ext
  intro e
  simp only [dfsEdges, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨ej,he,hpair⟩
    refine ⟨ej,he,?_⟩
    apply Subtype.ext
    have hp : s(e.val.1,e.val.2) =
        s((liftKeyEdge H q π ej).val.1,(liftKeyEdge H q π ej).val.2) :=
      hpair.trans (liftKeyEdge_sym2 H q π ej).symm
    rcases Sym2.eq_iff.mp hp with h | h
    · exact Prod.ext h.1.symm h.2.symm
    · have he := e.prop.1
      have hk := (liftKeyEdge H q π ej).prop.1
      omega
  · rintro ⟨ej,he,rfl⟩
    exact ⟨ej,he,liftKeyEdge_sym2 H q π ej⟩

 theorem dfsEdges_card (H : FiniteGraph) (q : ℕ) (π : Lift H q) (st : DFSState H q) :
    (dfsEdges H q π st).card = st.queried.card := by
  rw [dfsEdges_image]
  exact Finset.card_image_of_injective _ (liftKeyEdge_injective H q π)

end BuyAtBulk.EdgeOnlyGap.ProofA
