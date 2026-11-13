import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBResourceBoundary

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap.ProofB
attribute [local instance] Classical.propDecidable

/-- Zero extension from a route to the union of all used resources. -/
theorem sumUsedIndicator {A : Type} [Fintype A] [DecidableEq A] (U S : Finset A) (h : S ⊆ U)
    (F : A → ZMod 2) :
    (∑ a : U, if a.val ∈ S then F a.val else 0) = ∑ a ∈ S, F a := by
  classical
  rw [show (∑ a : U, if a.val ∈ S then F a.val else 0) =
    ∑ a ∈ U, if a ∈ S then F a else 0 from
      Finset.sum_coe_sort U (fun a => if a ∈ S then F a else 0),
    ← Finset.sum_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter]
  exact and_iff_right_of_imp (fun ha => h ha)

set_option maxHeartbeats 200000 in
/-- Each actual routing path has only its two endpoints as binary boundary. -/
theorem routingBoundary (D : BuyAtBulk.GraphData) [DecidableEq D.Vertex] (edge : EdgeOnlyInstance D)
    (r : D.toInstance.IntegralRouting) (i : Fin D.requestCount) (v : D.Vertex) :
    (∑ a : D.toInstance.usedResources r,
      if ∃ e, D.location a.val = Sum.inr e ∧ v ∈ e then
        (if a.val ∈ D.toInstance.uses (r.path i) then (1 : ZMod 2) else 0)
      else 0) =
      (if v = D.source i then 1 else 0) + (if v = D.target i then 1 else 0) := by
  classical
  have hsub : D.toInstance.uses (r.path i) ⊆ D.toInstance.usedResources r := by
    intro a ha
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ha⟩
  have hi : (D.decode (r.path i)).1 = i := by
    simpa only [BuyAtBulk.GraphData.toInstance, decide_eq_true_eq] using r.allowed_path i
  calc
    _ = ∑ a : D.toInstance.usedResources r,
        if a.val ∈ D.toInstance.uses (r.path i) then
          (if ∃ e, D.location a.val = Sum.inr e ∧ v ∈ e then (1 : ZMod 2) else 0)
        else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> rfl
    _ = ∑ a ∈ D.pathResources (D.decode (r.path i)),
        if ∃ e, D.location a = Sum.inr e ∧ v ∈ e then (1 : ZMod 2) else 0 :=
      by
        exact sumUsedIndicator (A := Fin D.resourceCount) _ _ hsub
          (fun a : Fin D.resourceCount =>
            if ∃ e, D.location a = Sum.inr e ∧ v ∈ e then (1 : ZMod 2) else 0)
    _ = _ := by
      have hb := resourcePathBoundary D edge (D.decode (r.path i)).1
        (D.decode (r.path i)).2 v
      exact hb.trans (by rw [hi])

end BuyAtBulk.EdgeOnlyGap.ProofB
