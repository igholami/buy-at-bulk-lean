import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBRankNullity
import BuyAtBulk.EdgeOnlyGap.Items.PortKernel
import BuyAtBulk.EdgeOnlyGap.Items.SpokeCount

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 800000 in
/-- Implicit rank–nullity and used-edge column count, p. 4, used in equation (7). -/
theorem portRankNullity (H : FiniteGraph) (q d : ℕ) (π : Lift H q) (hd : 0 < d)
    (r : (supplyData H q d π hd).toInstance.IntegralRouting) :
  Module.finrank (ZMod 2) (portKernel H q d π hd r) +
    Module.finrank (ZMod 2) (LinearMap.range (portBoundary H q d π hd r)) =
      spokeCount H q d π hd r + (usedCore H q d π hd r).card := by
  classical
  have hrn := ProofB.rankNullity (portBoundary H q d π hd r)
  rw [Fintype.card_coe] at hrn
  let U := (supplyData H q d π hd).toInstance.usedResources r
  let C := U.filter (coreResource H q d π hd)
  let S := U.filter fun a => ¬ coreResource H q d π hd a
  have hpart : S.card + C.card = U.card := by
    rw [add_comm]
    exact Finset.card_filter_add_card_filter_not _
  have hcore_card : C.card = (usedCore H q d π hd r).card := by
    let uncode := (Fintype.equivFin (Fin H.n × Fin q)).symm
    let φ : Edges (lifted H q π) → Sym2 (SupplyVertex H q) := fun e =>
      s(Sum.inr (uncode (finCongr (by simp [lifted]) e.val.1)),
        Sum.inr (uncode (finCongr (by simp [lifted]) e.val.2)))
    have hφ_inj : Function.Injective φ := by
      intro e₁ e₂ heq
      have hsym := Sym2.eq_iff.mp heq
      have hinj_v : Function.Injective (fun x : Fin (lifted H q π).n =>
          (Sum.inr (uncode (finCongr (by simp [lifted]) x)) : SupplyVertex H q)) :=
        Sum.inr_injective.comp (uncode.injective.comp (finCongr _).injective)
      rcases hsym with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Subtype.ext (Prod.ext (hinj_v h1) (hinj_v h2))
      · have := hinj_v h1
        have := hinj_v h2
        have := e₁.prop.1
        have := e₂.prop.1
        omega
    have hmap : ∀ a ∈ C, ∃ e ∈ usedCore H q d π hd r,
        (supplyData H q d π hd).location a = Sum.inr (φ e) := by
      intro a ha
      obtain ⟨haU, v, w, hloc⟩ := Finset.mem_filter.mp ha
      have hvalid := (supplyData H q d π hd).location_valid a
      rw [hloc] at hvalid
      change (supplyGraph H q π).Adj (Sum.inr v) (Sum.inr w) at hvalid
      dsimp [supplyGraph] at hvalid
      rw [SimpleGraph.fromRel_adj] at hvalid
      obtain ⟨_, hrel⟩ := hvalid
      have hadj_lift : (liftGraph H q π).Adj v w := by
        rcases hrel with (⟨_, _, h1, _⟩ | ⟨a', b', h1, h2, hadj⟩) |
                         (⟨_, _, h1, _⟩ | ⟨a', b', h1, h2, hadj⟩)
        · cases h1
        · cases Sum.inr.inj h1; cases Sum.inr.inj h2; exact hadj
        · cases h1
        · cases Sum.inr.inj h1; cases Sum.inr.inj h2; exact hadj.symm
      let cv : Fin (lifted H q π).n := (finCongr (by simp [lifted])).symm (uncode.symm v)
      let cw : Fin (lifted H q π).n := (finCongr (by simp [lifted])).symm (uncode.symm w)
      have hadj_lifted : (lifted H q π).graph.Adj cv cw := by
        change (liftGraph H q π).Adj (uncode (finCongr _ cv)) (uncode (finCongr _ cw))
        simpa [cv, cw] using hadj_lift
      rcases lt_or_gt_of_ne hadj_lifted.ne with hlt | hgt
      · let e : Edges (lifted H q π) := ⟨(cv, cw), hlt, hadj_lifted⟩
        have hφe : φ e = s(Sum.inr v, Sum.inr w) := by
          dsimp only [φ, e, cv, cw]
          simp only [Equiv.apply_symm_apply]
        refine ⟨e, ?_, hloc.trans (congrArg Sum.inr hφe.symm)⟩
        simp only [usedCore, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨a, haU, hloc.trans (congrArg Sum.inr hφe.symm)⟩
      · let e : Edges (lifted H q π) := ⟨(cw, cv), hgt, hadj_lifted.symm⟩
        have hφe : φ e = s(Sum.inr v, Sum.inr w) := by
          dsimp only [φ, e, cv, cw]
          simp only [Equiv.apply_symm_apply]
          exact Sym2.eq_swap
        refine ⟨e, ?_, hloc.trans (congrArg Sum.inr hφe.symm)⟩
        simp only [usedCore, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨a, haU, hloc.trans (congrArg Sum.inr hφe.symm)⟩
    refine (Finset.card_bij (fun (e : Edges (lifted H q π)) (he : e ∈ usedCore H q d π hd r) =>
      Classical.choose ((Finset.mem_filter.mp he).2))
      (fun e he => by
        have hspec := Classical.choose_spec ((Finset.mem_filter.mp he).2)
        refine Finset.mem_filter.mpr ⟨hspec.1, _, _, hspec.2⟩)
      (fun e₁ he₁ e₂ he₂ heq => by
        have hspec₁ := (Classical.choose_spec ((Finset.mem_filter.mp he₁).2)).2
        have hspec₂ := (Classical.choose_spec ((Finset.mem_filter.mp he₂).2)).2
        have hloc_eq : (supplyData H q d π hd).location (Classical.choose ((Finset.mem_filter.mp he₁).2)) =
            (supplyData H q d π hd).location (Classical.choose ((Finset.mem_filter.mp he₂).2)) :=
          congrArg (supplyData H q d π hd).location heq
        rw [hspec₁, hspec₂] at hloc_eq
        exact hφ_inj (Sum.inr.inj hloc_eq))
      (fun a ha => by
        obtain ⟨e, he, hloc⟩ := hmap a ha
        refine ⟨e, he, ?_⟩
        apply (supplyData H q d π hd).location_injective
        have hspec := (Classical.choose_spec ((Finset.mem_filter.mp he).2)).2
        exact hspec.trans hloc.symm)).symm
  change Module.finrank (ZMod 2) (portKernel H q d π hd r) +
      Module.finrank (ZMod 2) (LinearMap.range (portBoundary H q d π hd r)) =
      S.card + (usedCore H q d π hd r).card
  change Module.finrank (ZMod 2) (LinearMap.ker (portBoundary H q d π hd r)) +
    Module.finrank (ZMod 2) (LinearMap.range (portBoundary H q d π hd r)) = _
  exact hrn.trans (hpart.symm.trans (congrArg (fun n => S.card + n) hcore_card))

end BuyAtBulk.EdgeOnlyGap
