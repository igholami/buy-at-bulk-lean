import BuyAtBulk.EdgeOnlyGap.Items.FullBoundary
import BuyAtBulk.EdgeOnlyGap.Items.DefinedFullBoundary
import BuyAtBulk.EdgeOnlyGap.Items.CollapseVertex
import BuyAtBulk.EdgeOnlyGap.Items.RouteChain
import BuyAtBulk.EdgeOnlyGap.Items.ChainProjection
import BuyAtBulk.EdgeOnlyGap.Items.PortKernel
import BuyAtBulk.EdgeOnlyGap.Items.EdgeOnlyInstance
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBRoutingBoundary
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBProjectionCommutation

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 4: boundary commutes with projection and vertex collapse; each route lies in Z. -/
theorem projectionBoundary (H : FiniteGraph) (q d : ℕ) (π : Lift H q) (hd : 0 < d)
    (r : (supplyData H q d π hd).toInstance.IntegralRouting) :
  (∀ z v, baseBoundary H (chainProjection H q d π hd r z) v =
    ∑ w : SupplyVertex H q, if collapseVertex H q w = v then
      fullBoundary H q d π hd r z w else 0) ∧
  (∀ i, routeChain H q d π hd r i ∈ portKernel H q d π hd r ∧
    ∀ v, baseBoundary H (chainProjection H q d π hd r (routeChain H q d π hd r i)) v =
      (if v=((Fintype.equivFin (Edges H)).symm i).val.1 then 1 else 0) +
      (if v=((Fintype.equivFin (Edges H)).symm i).val.2 then 1 else 0)) := by
  classical
  let D := supplyData H q d π hd
  let enum := (Fintype.equivFin (supplyGraph H q π).edgeSet).symm
  have hedge : EdgeOnlyInstance D := by
    refine ⟨fun _ => rfl, fun a => ⟨(enum a).val, rfl⟩, ?_⟩
    intro e he
    refine ⟨enum.symm ⟨e,he⟩, ?_⟩
    change Sum.inr (enum (enum.symm ⟨e,he⟩)).val = Sum.inr e
    rw [enum.apply_symm_apply]
    rfl
  have hfull (i : Fin (requests H)) (w : SupplyVertex H q) :
      fullBoundary H q d π hd r (routeChain H q d π hd r i) w =
      (if w = (Sum.inl (((Fintype.equivFin (Edges H)).symm i).val.1) : SupplyVertex H q) then 1 else 0) + (if w = (Sum.inl (((Fintype.equivFin (Edges H)).symm i).val.2) : SupplyVertex H q) then 1 else 0) := by
    change (∑ a : D.toInstance.usedResources r,
      if ∃ e, D.location a.val = Sum.inr e ∧ w ∈ e then
        (if a.val ∈ D.toInstance.uses (r.path i) then (1 : ZMod 2) else 0) else 0) = _
    have hb := @ProofB.routingBoundary D
      (inferInstance : DecidableEq (SupplyVertex H q)) hedge r i w
    refine Eq.trans ?_ (hb.trans ?_)
    · apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> first | rfl | contradiction
    · change (if w = (Sum.inl _ : SupplyVertex H q) then (1 : ZMod 2) else 0) +
        (if w = (Sum.inl _ : SupplyVertex H q) then 1 else 0) = _
      split_ifs <;> first | rfl | contradiction
  have hcomm := ProofB.projectionCommutation H q d π hd r
  refine ⟨hcomm, ?_⟩
  intro i
  constructor
  · change portBoundary H q d π hd r (routeChain H q d π hd r i) = 0
    ext w
    change fullBoundary H q d π hd r (routeChain H q d π hd r i) (Sum.inr w) = 0
    rw [hfull]
    simp
  · intro v
    rw [hcomm]
    simp_rw [hfull]
    have hsum (u : SupplyVertex H q) :
        (∑ w : SupplyVertex H q, if collapseVertex H q w = v then
          (if w = u then (1 : ZMod 2) else 0) else 0) =
        if collapseVertex H q u = v then 1 else 0 := by
      rw [Finset.sum_eq_single u]
      · simp
      · intro w hw hwu
        simp [hwu]
      · simp
    have hdist (w : SupplyVertex H q) :
        (if collapseVertex H q w = v then
          (if w = (Sum.inl (((Fintype.equivFin (Edges H)).symm i).val.1) : SupplyVertex H q) then (1 : ZMod 2) else 0) +
          (if w = (Sum.inl (((Fintype.equivFin (Edges H)).symm i).val.2) : SupplyVertex H q) then 1 else 0) else 0) =
        (if collapseVertex H q w = v then
          (if w = (Sum.inl (((Fintype.equivFin (Edges H)).symm i).val.1) : SupplyVertex H q) then 1 else 0) else 0) +
        (if collapseVertex H q w = v then
          (if w = (Sum.inl (((Fintype.equivFin (Edges H)).symm i).val.2) : SupplyVertex H q) then 1 else 0) else 0) := by
      split_ifs <;> first | rfl | contradiction
    simp_rw [hdist]
    rw [Finset.sum_add_distrib, hsum, hsum]
    simp only [D, supplyData, collapseVertex, eq_comm]

end BuyAtBulk.EdgeOnlyGap
