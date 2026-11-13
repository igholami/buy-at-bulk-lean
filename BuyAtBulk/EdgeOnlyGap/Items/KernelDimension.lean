import Mathlib.LinearAlgebra.Dimension.Finrank
import BuyAtBulk.EdgeOnlyGap.Items.PortKernel
import BuyAtBulk.EdgeOnlyGap.Items.PortRankNullity
import BuyAtBulk.EdgeOnlyGap.Items.IncidenceRank
import BuyAtBulk.EdgeOnlyGap.Items.CycleRankFormula

set_option maxHeartbeats 800000
noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Equation (7), p. 4: adding spoke columns cannot decrease rank. -/
theorem kernelDimension (H : FiniteGraph) (q d : ℕ) (π : Lift H q) (hd : 0 < d)
    (r : (supplyData H q d π hd).toInstance.IntegralRouting) :
  (edgeSupport (lifted H q π) (usedCore H q d π hd r)).card -
    edgeComponents (lifted H q π) (usedCore H q d π hd r) ≤
    Module.finrank (ZMod 2) (LinearMap.range (portBoundary H q d π hd r)) ∧
  Module.finrank (ZMod 2) (portKernel H q d π hd r) ≤
    spokeCount H q d π hd r + beta (lifted H q π) (usedCore H q d π hd r) := by
  classical
  let D := supplyData H q d π hd
  let W := usedCore H q d π hd r
  let U := {a // a ∈ D.toInstance.usedResources r}
  let E : Fin (lifted H q π).n ≃ (Fin H.n × Fin q) :=
    (finCongr (by simp [lifted])).trans (Fintype.equivFin (Fin H.n × Fin q)).symm
  have hex (e : W) : ∃ a ∈ D.toInstance.usedResources r,
      D.location a = Sum.inr (s(Sum.inr (E e.val.val.1), Sum.inr (E e.val.val.2))) := by
    have he := e.property
    simp only [W, usedCore, Finset.mem_filter, Finset.mem_univ, true_and] at he
    exact he
  let f : W → U := fun e => ⟨Classical.choose (hex e), (Classical.choose_spec (hex e)).1⟩
  have hloc (e : W) : D.location (f e).val =
      Sum.inr (s(Sum.inr (E e.val.val.1), Sum.inr (E e.val.val.2))) :=
    (Classical.choose_spec (hex e)).2
  have hcolumn (e : W) (v : Fin (lifted H q π).n) :
      portBoundary H q d π hd r (Pi.single (f e) 1) (E v) =
        if v = e.val.val.1 ∨ v = e.val.val.2 then 1 else 0 := by
    change (∑ a : U, if ∃ t, D.location a.val = Sum.inr t ∧ Sum.inr (E v) ∈ t then
      (Pi.single (f e) (1 : ZMod 2)) a else 0) = _
    rw [Finset.sum_eq_single (f e)]
    · have hi : (∃ t, D.location (f e).val = Sum.inr t ∧ Sum.inr (E v) ∈ t) ↔
          (v = e.val.val.1 ∨ v = e.val.val.2) := by
        constructor
        · rintro ⟨t, ht, hv⟩
          have ht' := Sum.inr.inj ((hloc e).symm.trans ht)
          rw [← ht'] at hv
          rcases Sym2.mem_iff.mp hv with hv | hv
          · exact Or.inl (E.injective (Sum.inr.inj hv))
          · exact Or.inr (E.injective (Sum.inr.inj hv))
        · intro hv
          refine ⟨_, hloc e, ?_⟩
          apply Sym2.mem_iff.mpr
          rcases hv with hv | hv
          · exact Or.inl (congrArg (fun x => Sum.inr (E x)) hv)
          · exact Or.inr (congrArg (fun x => Sum.inr (E x)) hv)
      simp only [Pi.single_eq_same]
      exact if_congr hi rfl rfl
    · intro a _ hne
      simp [Pi.single_apply, hne]
    · simp
  let R : ((Fin H.n × Fin q) → ZMod 2) →ₗ[ZMod 2]
      (Fin (lifted H q π).n → ZMod 2) :=
    { toFun := fun z v => z (E v)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hincl : LinearMap.range (boundary (lifted H q π) W) ≤
      LinearMap.range (R.comp (portBoundary H q d π hd r)) := by
    rintro _ ⟨z, rfl⟩
    refine ⟨∑ e : W, z e • Pi.single (f e) (1 : ZMod 2), ?_⟩
    simp only [LinearMap.comp_apply, map_sum, map_smul]
    funext v
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change (∑ e : W, z e * portBoundary H q d π hd r (Pi.single (f e) 1) (E v)) =
      ∑ e : W, if v = e.val.val.1 ∨ v = e.val.val.2 then z e else 0
    apply Finset.sum_congr rfl
    intro e _
    rw [hcolumn]
    split_ifs <;> simp
  have hle : (edgeSupport (lifted H q π) W).card - edgeComponents (lifted H q π) W ≤
      Module.finrank (ZMod 2) (LinearMap.range (portBoundary H q d π hd r)) := by
    rw [← incidenceRank]
    refine (Submodule.finrank_mono hincl).trans ?_
    rw [LinearMap.range_comp]
    exact Submodule.finrank_map_le _ _
  refine ⟨hle, ?_⟩
  have hrn := portRankNullity H q d π hd r
  have hb := (cycleRankFormula (lifted H q π) W).2
  have hc : edgeComponents (lifted H q π) W ≤ (edgeSupport (lifted H q π) W).card :=
    Finset.card_image_le
  change Module.finrank (ZMod 2) (portKernel H q d π hd r) ≤
    spokeCount H q d π hd r + beta (lifted H q π) W
  change Module.finrank (ZMod 2) (portKernel H q d π hd r) +
    Module.finrank (ZMod 2) (LinearMap.range (portBoundary H q d π hd r)) =
      spokeCount H q d π hd r + W.card at hrn
  omega

end BuyAtBulk.EdgeOnlyGap
