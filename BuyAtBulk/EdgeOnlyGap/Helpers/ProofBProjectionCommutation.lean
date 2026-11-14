import BuyAtBulk.EdgeOnlyGap.Items.FullBoundary
import BuyAtBulk.EdgeOnlyGap.Items.DefinedFullBoundary
import BuyAtBulk.EdgeOnlyGap.Items.ChainProjection
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBProjectionColumn

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap.ProofB
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 800000 in
/-- Summing the individual supply-edge identities gives chain-level commutation. -/
theorem projectionCommutation (H : FiniteGraph) (q d : ℕ) (π : Lift H q) (hd : 0 < d)
    (r : (supplyData H q d π hd).toInstance.IntegralRouting)
    (z : UsedChains H q d π hd r) (v : Fin H.n) :
    baseBoundary H (chainProjection H q d π hd r z) v =
      ∑ w : SupplyVertex H q, if collapseVertex H q w = v then
        fullBoundary H q d π hd r z w else 0 := by
  classical
  let D := supplyData H q d π hd
  let A := {a // a ∈ D.toInstance.usedResources r}
  let enum := (Fintype.equivFin (supplyGraph H q π).edgeSet).symm
  have hloc (a : Fin D.resourceCount) : D.location a = Sum.inr (enum a).val := rfl
  change (∑ e : Edges H, if v = e.val.1 ∨ v = e.val.2 then
    (∑ a : A, if ∃ j k : Fin q, D.location a.val =
      Sum.inr (s(Sum.inr (e.val.1,j),Sum.inr (e.val.2,k))) then z a else 0)
    else 0) = ∑ w : SupplyVertex H q, if collapseVertex H q w = v then
      (∑ a : A, if ∃ e, D.location a.val = Sum.inr e ∧ w ∈ e then z a else 0) else 0
  have hleft (e : Edges H) :
      (if v = e.val.1 ∨ v = e.val.2 then
        (∑ a : A, if ∃ j k : Fin q, D.location a.val =
          Sum.inr (s(Sum.inr (e.val.1,j),Sum.inr (e.val.2,k))) then z a else 0)
        else 0) =
      ∑ a : A, if v = e.val.1 ∨ v = e.val.2 then
        (if ∃ j k : Fin q, D.location a.val =
          Sum.inr (s(Sum.inr (e.val.1,j),Sum.inr (e.val.2,k))) then z a else 0) else 0 := by
    split_ifs <;> simp
  have hright (w : SupplyVertex H q) :
      (if collapseVertex H q w = v then
        (∑ a : A, if ∃ e, D.location a.val = Sum.inr e ∧ w ∈ e then z a else 0) else 0) =
      ∑ a : A, if collapseVertex H q w = v then
        (if ∃ e, D.location a.val = Sum.inr e ∧ w ∈ e then z a else 0) else 0 := by
    split_ifs <;> simp
  simp_rw [hleft, hright]
  refine (Finset.sum_comm).trans ?_
  refine Eq.trans ?_ (Finset.sum_comm).symm
  apply Finset.sum_congr rfl
  intro a _
  have hh := projectionColumn H q π (enum a.val).val (enum a.val).property v (z a)
  have hcore (e : Edges H) :
      (∃ j k : Fin q, D.location a.val =
        Sum.inr (s(Sum.inr (e.val.1,j),Sum.inr (e.val.2,k)))) ↔
      ∃ j k : Fin q, (enum a.val).val =
        s(Sum.inr (e.val.1,j),Sum.inr (e.val.2,k)) := by
    constructor
    · rintro ⟨j,k,h⟩
      exact ⟨j,k,Sum.inr.inj ((hloc a.val).symm.trans h)⟩
    · rintro ⟨j,k,h⟩
      exact ⟨j,k,(hloc a.val).trans (congrArg Sum.inr h)⟩
  have hinc (w : SupplyVertex H q) :
      (∃ e, D.location a.val = Sum.inr e ∧ w ∈ e) ↔ w ∈ (enum a.val).val := by
    constructor
    · rintro ⟨e,he,hw⟩
      have he' : (enum a.val).val = e := Sum.inr.inj ((hloc a.val).symm.trans he)
      exact he'.symm ▸ hw
    · intro hw
      exact ⟨_,hloc a.val,hw⟩
  simpa only [hcore, hinc] using hh

end BuyAtBulk.EdgeOnlyGap.ProofB
