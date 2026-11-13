import BuyAtBulk.EdgeOnlyGap.Helpers.ProofADFSSearch
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofADFSKeySupport
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofADFSConnectedClosure

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

/-- Actual terminating replay of exactly the chosen connected edge set. -/
theorem dfsCompleteSearch (H : FiniteGraph) (q d : ℕ) (ports : PortTable H d) (π : Lift H q)
    (W : Finset (Edges (lifted H q π))) (connected : edgeComponents (lifted H q π) W = 1)
    (root : Fin H.n × Fin q) (root_mem : liftCode H q π root ∈ edgeSupport (lifted H q π) W) :
    ∃ (script : List (DFSSymbol d)) (st : DFSState H q),
      dfsReplay H q d ports π root script = some st ∧ st.stack = [root] ∧
      dfsEdges H q π st = W ∧ st.visited.card = (edgeSupport (lifted H q π) W).card := by
  let allowed : Finset (Edges H × Fin q) := Finset.univ.filter fun ej => liftKeyEdge H q π ej ∈ W
  have himage : allowed.image (liftKeyEdge H q π) = W := by
    ext e
    simp only [allowed,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨ej,he,rfl⟩; exact he
    · intro he
      obtain ⟨ej,rfl⟩ := (liftKeyEdge_bijective H q π).2 e
      exact ⟨ej,he,rfl⟩
  have hroot : root ∈ keySupport H q π allowed := by
    have hm : liftCode H q π root ∈ (keySupport H q π allowed).image (liftCode H q π) := by
      rw [keySupport_image,himage]
      exact root_mem
    obtain ⟨x,hx,heq⟩ := Finset.mem_image.mp hm
    exact (liftCode H q π).injective heq ▸ hx
  let initial : DFSState H q := ⟨[root],{root},∅,0⟩
  have hi : SearchInvariant H q π allowed root initial := by
    refine ⟨⟨[],rfl⟩,?_,Finset.empty_subset _,?_,?_,?_⟩
    · intro x hx; simpa [initial] using hx
    · exact Finset.singleton_subset_iff.mpr hroot
    · simp [initial]
    · intro x hx hn
      simp only [initial,Finset.mem_singleton] at hx
      simp [initial,hx] at hn
  obtain ⟨script,st,run,inv,hstack,hclose⟩ := dfsSearch H q d ports π allowed root initial hi
  let S := st.visited.image (liftCode H q π)
  have hrS : liftCode H q π root ∈ S :=
    Finset.mem_image_of_mem _ (inv.stackVisited root (by simp [hstack]))
  have hSsupport : S ⊆ edgeSupport (lifted H q π) W := by
    rw [← himage,← keySupport_image]
    exact Finset.image_mono _ inv.visitedSupport
  have hsupportS : edgeSupport (lifted H q π) W ⊆ S := by
    apply connected_support_closed (lifted H q π) W connected S (liftCode H q π root) hrS root_mem
    intro e he hmeet
    obtain ⟨ej,hej,heq⟩ := Finset.mem_image.mp (himage.symm ▸ he)
    subst e
    have hkey : ej ∈ st.queried := by
      rcases hmeet with hm | hm
      · obtain ⟨x,hx,hcode⟩ := Finset.mem_image.mp hm
        exact hclose x hx ej hej ((keyIncident_iff H q π ej x).mpr (Or.inl hcode))
      · obtain ⟨x,hx,hcode⟩ := Finset.mem_image.mp hm
        exact hclose x hx ej hej ((keyIncident_iff H q π ej x).mpr (Or.inr hcode))
    have hL := Finset.mem_image_of_mem (liftCode H q π) (inv.endpoints ej hkey).1
    have hR := Finset.mem_image_of_mem (liftCode H q π) (inv.endpoints ej hkey).2
    rcases Sym2.eq_iff.mp (liftKeyEdge_sym2 H q π ej) with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · exact ⟨hl.symm ▸ hL,hr.symm ▸ hR⟩
    · exact ⟨hl.symm ▸ hR,hr.symm ▸ hL⟩
  have hS : S = edgeSupport (lifted H q π) W := Finset.Subset.antisymm hSsupport hsupportS
  have hqueried : st.queried = allowed := by
    apply Finset.Subset.antisymm inv.selected
    intro ej hej
    have hleftSupport : keyLeft H q ej ∈ keySupport H q π allowed :=
      keySupport_mem H q π allowed ej hej _ (Or.inl rfl)
    have hm : liftCode H q π (keyLeft H q ej) ∈ S := by
      rw [hS,← himage,← keySupport_image]
      exact Finset.mem_image_of_mem _ hleftSupport
    obtain ⟨x,hx,heq⟩ := Finset.mem_image.mp hm
    have hxleft : x = keyLeft H q ej := (liftCode H q π).injective heq
    exact hclose x hx ej hej (Or.inl hxleft)
  refine ⟨script,st,run,hstack,?_,?_⟩
  · rw [dfsEdges_image,hqueried,himage]
  · have hc : S.card = st.visited.card := Finset.card_image_of_injective _ (liftCode H q π).injective
    rw [hS] at hc
    exact hc.symm

end BuyAtBulk.EdgeOnlyGap.ProofA
