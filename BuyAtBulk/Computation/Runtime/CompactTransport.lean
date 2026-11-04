import BuyAtBulk.Model.CompactFlowOptimizer

/-! Exact graph-isomorphism transport of compact flows and both budgets. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace BuyAtBulk.CompactFlow.Solution
variable {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W} {h : ℕ}

def mapIso (f : Solution G h) (iso : G ≃g H) : Solution H h where
  source i := iso (f.source i)
  target i := iso (f.target i)
  buying w := f.buying (iso.symm w)
  physical w := f.physical (iso.symm w)
  demand := f.demand
  opening w := f.opening (iso.symm w)
  node i w := f.node i (iso.symm w)
  transport i u v := f.transport i (iso.symm u) (iso.symm v)
  buying_nonneg w := f.buying_nonneg _
  physical_nonneg w := f.physical_nonneg _
  demand_pos := f.demand_pos
  opening_bounds w := f.opening_bounds _
  node_nonneg i w := f.node_nonneg i _
  transport_nonneg i u v := f.transport_nonneg i _ _
  transport_nonedge := by
    intro i u v nonedge
    apply f.transport_nonedge
    exact fun edge => nonedge (iso.symm.map_rel_iff.mp edge)
  capacity i w := f.capacity i _
  incoming_balance := by
    intro i w
    classical
    have sum : (∑ u : W,f.transport i (iso.symm u) (iso.symm w)) =
        ∑ u : V,f.transport i u (iso.symm w) :=
      Fintype.sum_equiv iso.symm.toEquiv _ _ (by intro u;rfl)
    rw [sum,f.incoming_balance]
    have eq : (iso (f.source i)=w) ↔ f.source i=iso.symm w := iso.toEquiv.apply_eq_iff_eq_symm_apply
    simp only [eq]
  outgoing_balance := by
    intro i w
    classical
    have sum : (∑ u : W,f.transport i (iso.symm w) (iso.symm u)) =
        ∑ u : V,f.transport i (iso.symm w) u :=
      Fintype.sum_equiv iso.symm.toEquiv _ _ (by intro u;rfl)
    rw [sum,f.outgoing_balance]
    have eq : (iso (f.target i)=w) ↔ f.target i=iso.symm w := iso.toEquiv.apply_eq_iff_eq_symm_apply
    simp only [eq]
  source_buying i := by simpa using f.source_buying i
  source_physical i := by simpa using f.source_physical i
  target_buying i := by simpa using f.target_buying i
  target_physical i := by simpa using f.target_physical i

@[simp] theorem mapIso_buying (f : Solution G h) (iso : G ≃g H) :
    (f.mapIso iso).buyingBudget=f.buyingBudget := by
  classical
  exact Fintype.sum_equiv iso.symm.toEquiv _ _ (by intro w;rfl)
@[simp] theorem mapIso_length (f : Solution G h) (iso : G ≃g H) (i : Fin h) :
    (f.mapIso iso).fractionalLength i=f.fractionalLength i := by
  classical
  exact Fintype.sum_equiv iso.symm.toEquiv _ _ (by intro w;rfl)
@[simp] theorem mapIso_rental (f : Solution G h) (iso : G ≃g H) :
    (f.mapIso iso).rentalBudget=f.rentalBudget := by
  simp only [rentalBudget,mapIso_length]
  rfl

theorem mapIso_sameData (f g : Solution G h) (same : f.SameData g) (iso : G ≃g H) :
    (f.mapIso iso).SameData (g.mapIso iso) := by
  rcases same with ⟨source,target,buying,physical,demand⟩
  exact ⟨congrArg (fun source i => iso (source i)) source,
    congrArg (fun target i => iso (target i)) target,
    congrArg (fun buying w => buying (iso.symm w)) buying,
    congrArg (fun physical w => physical (iso.symm w)) physical,demand⟩

end BuyAtBulk.CompactFlow.Solution
