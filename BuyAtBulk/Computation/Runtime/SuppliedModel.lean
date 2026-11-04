import BuyAtBulk.Computation.ShortestPath
import BuyAtBulk.UpperBound.NodeLP

/-! Proof-only transport of the supplied path LP to the computed reduced graph.
This preserves the original per-request lengths, without recomputing an LP. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace BuyAtBulk.Computation.Runtime.Supplied
open BuyAtBulk.UpperBound
variable {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}

 def pathEquiv (iso : G ≃g H) (s t : V) : G.Path s t ≃ H.Path (iso s) (iso t) where
  toFun p := p.map iso.toHom iso.injective
  invFun p := ShortestPath.copyPath (p.map iso.symm.toHom iso.symm.injective) (iso.symm_apply_apply s) (iso.symm_apply_apply t)
  left_inv p := by
    apply Subtype.ext
    apply SimpleGraph.Walk.ext_support
    simp only [SimpleGraph.Path.map,ShortestPath.copyPath,SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_map,List.map_map]
    simp [Function.comp_def]
  right_inv p := by
    apply Subtype.ext
    apply SimpleGraph.Walk.ext_support
    simp only [SimpleGraph.Path.map,ShortestPath.copyPath,SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_map,List.map_map]
    simp [Function.comp_def]

 theorem pathEquiv_mem (iso : G ≃g H) (s t : V) (p : G.Path s t) (w : W) :
    w ∈ ((pathEquiv iso s t) p).val.support ↔ iso.symm w ∈ p.val.support := by
  simp only [pathEquiv,Equiv.coe_fn_mk,SimpleGraph.Path.map,SimpleGraph.Walk.support_map,List.mem_map]
  constructor
  · rintro ⟨v,mem,equal⟩
    have : v=iso.symm w := iso.toEquiv.eq_symm_apply.mpr equal
    simpa only [←this] using mem
  · intro mem
    exact ⟨iso.symm w,mem,iso.apply_symm_apply w⟩

 theorem pathEquiv_weight (iso : G ≃g H) (s t : V) (p : G.Path s t) (cost : V → ℚ) :
    NodeMetric.walkWeight H (fun w=>cost (iso.symm w)) ((pathEquiv iso s t) p).val =
      NodeMetric.walkWeight G cost p.val := by
  classical
  unfold NodeMetric.walkWeight
  have expand {X : Type} [Fintype X] (S : Finset X) (f : X → ℚ) : (∑ a ∈ S,f a) = ∑ a,if a ∈ S then f a else 0 := by simp
  rw [expand (((pathEquiv iso s t) p).val.support.toFinset) (fun w=>cost (iso.symm w)), expand p.val.support.toFinset cost]
  apply Fintype.sum_equiv iso.symm.toEquiv
  intro w
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,List.mem_toFinset,pathEquiv_mem]
  rfl

 def mapLP {h : ℕ} (lp : NodeLP G h) (iso : G ≃g H) : NodeLP H h := by
  classical
  let e (i : Fin h) := pathEquiv iso (lp.source i) (lp.target i)
  refine {
    source i := iso (lp.source i)
    target i := iso (lp.target i)
    buying w := lp.buying (iso.symm w)
    physical w := lp.physical (iso.symm w)
    demand := lp.demand
    opening w := lp.opening (iso.symm w)
    flow i p := lp.flow i ((e i).symm p)
    buying_nonneg w := lp.buying_nonneg _
    physical_nonneg w := lp.physical_nonneg _
    demand_pos := lp.demand_pos
    opening_bounds w := lp.opening_bounds _
    flow_nonneg i p := lp.flow_nonneg i _
    unit i := ?_
    capacity i w := ?_
    source_buying i := by simpa using lp.source_buying i
    source_physical i := by simpa using lp.source_physical i
    target_buying i := by simpa using lp.target_buying i
    target_physical i := by simpa using lp.target_physical i }
  · exact (Fintype.sum_equiv (e i).symm _ _ (by intro p;rfl)).trans (lp.unit i)
  · have eq : (∑ p : H.Path (iso (lp.source i)) (iso (lp.target i)),
        if w ∈ p.val.support then lp.flow i ((e i).symm p) else 0) =
      ∑ p : G.Path (lp.source i) (lp.target i), if iso.symm w ∈ p.val.support then lp.flow i p else 0 := by
      symm
      apply Fintype.sum_equiv (e i)
      intro p
      simp only [Equiv.symm_apply_apply]
      simp only [e,pathEquiv_mem]
    exact eq.trans_le (lp.capacity i _)

 theorem mapLP_buying {h : ℕ} (lp : NodeLP G h) (iso : G ≃g H) :
    (mapLP lp iso).buyingBudget=lp.buyingBudget := by
  classical
  exact Fintype.sum_equiv iso.symm.toEquiv _ _ (by intro w;rfl)

 theorem mapLP_length {h : ℕ} (lp : NodeLP G h) (iso : G ≃g H) (i : Fin h) :
    (mapLP lp iso).fractionalLength i=lp.fractionalLength i := by
  classical
  symm
  apply Fintype.sum_equiv (pathEquiv iso (lp.source i) (lp.target i))
  intro p
  simp only [NodeLP.fractionalLength,mapLP,Equiv.symm_apply_apply,pathEquiv_weight]

 theorem mapLP_rental {h : ℕ} (lp : NodeLP G h) (iso : G ≃g H) :
    (mapLP lp iso).rentalBudget=lp.rentalBudget := by
  unfold NodeLP.rentalBudget
  simp only [mapLP_length]
  rfl

end BuyAtBulk.Computation.Runtime.Supplied
