import BuyAtBulk.Computation.Rounding.Algorithm
import BuyAtBulk.UpperBound.ZeroLengthLP

/-! A proof-only view of the zero-length LP with the exact metadata target
function used by executable rounding. Only endpoint casts transport flows;
all original buying data and the original request count are retained. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.Computation.Rounding
open BuyAtBulk.UpperBound
variable {V : Type} [Fintype V] {G : SimpleGraph V} {h : ℕ} (lp : NodeLP G h)
local instance : DecidableEq V := Classical.decEq V
local instance : DecidableRel G.Adj := Classical.decRel _
local instance : DecidableRel (zeroGraph G lp.physical).Adj := Classical.decRel _

private theorem castPath_support {H : SimpleGraph V} {s t t' : V} (equal : t' = t) (path : H.Path s t') :
    ((Equiv.cast (congrArg (fun v => H.Path s v) equal)) path).val.support = path.val.support := by
  cases equal
  rfl

theorem zeroTarget_eq (lengths : Fin h → ℚ) (metadata : ∀ i, lengths i = lp.fractionalLength i) (i : Fin h) :
    lp.zeroNodeLP.target i = zeroTarget lp.source lp.target lengths i := by
  by_cases zero : lp.fractionalLength i = 0
  · simp [NodeLP.zeroNodeLP, NodeLP.zeroCommodity, zeroTarget, metadata i, zero]
  · simp [NodeLP.zeroNodeLP, NodeLP.zeroCommodity, zeroTarget, metadata i, zero]

theorem source_opening_eq_one (i : Fin h) : lp.opening (lp.source i) = 1 := by
  classical
  have bound := lp.capacity i (lp.source i)
  have member (path : G.Path (lp.source i) (lp.target i)) : lp.source i ∈ path.val.support :=
    path.val.start_mem_support
  simp only [member, ite_true, lp.unit] at bound
  exact le_antisymm (lp.opening_bounds _).2 bound

private theorem zeroNodeLP_original_capacity (i : Fin h) (v : V) :
    (∑ path : (zeroGraph G lp.physical).Path (lp.zeroNodeLP.source i) (lp.zeroNodeLP.target i),
      if v ∈ path.val.support then lp.zeroNodeLP.flow i path else 0) ≤ lp.opening v := by
  classical
  let property (commodity : FreeCommodity (zeroGraph G lp.physical) lp.buying lp.raisedOpening (lp.source i)) : Prop :=
    (∑ path : (zeroGraph G lp.physical).Path (lp.source i) commodity.target,
      if v ∈ path.val.support then commodity.flow path else 0) ≤ lp.opening v
  change property (lp.zeroCommodity i)
  unfold NodeLP.zeroCommodity
  split_ifs with zero
  · exact (lp.zeroFlow_resource i zero v).trans_le (lp.capacity i v)
  · dsimp only [property]
    let nil : (zeroGraph G lp.physical).Path (lp.source i) (lp.source i) := SimpleGraph.Path.nil
    rw [Finset.sum_eq_single nil]
    · by_cases same : v = lp.source i
      · subst v
        simp [nil, SimpleGraph.Path.nil, source_opening_eq_one]
      · simp [nil, SimpleGraph.Path.nil, same, (lp.opening_bounds v).1]
    · intro path _ ne
      have ne' : path ≠ SimpleGraph.Path.nil := ne
      simp [ne']
    · simp

def zeroMetadataLP (lengths : Fin h → ℚ) (metadata : ∀ i, lengths i = lp.fractionalLength i) :
    NodeLP (zeroGraph G lp.physical) h := by
  classical
  let e (i : Fin h) : (zeroGraph G lp.physical).Path (lp.source i) (zeroTarget lp.source lp.target lengths i) ≃
      (zeroGraph G lp.physical).Path (lp.zeroNodeLP.source i) (lp.zeroNodeLP.target i) :=
    Equiv.cast (congrArg (fun v => (zeroGraph G lp.physical).Path (lp.source i) v)
      (zeroTarget_eq lp lengths metadata i).symm)
  refine {
    source := lp.source
    target := zeroTarget lp.source lp.target lengths
    buying := lp.buying
    physical := fun _ => 0
    demand := lp.demand
    opening := restrictedOpening lp.buying lp.physical lp.opening
    flow i path := lp.zeroNodeLP.flow i (e i path)
    buying_nonneg := lp.buying_nonneg
    physical_nonneg _ := le_rfl
    demand_pos := lp.demand_pos
    opening_bounds := by
      intro v
      by_cases hv : lp.physical v = 0
      · simpa [restrictedOpening, hv] using lp.opening_bounds v
      · simp [restrictedOpening, hv]
    flow_nonneg i path := lp.zeroNodeLP.flow_nonneg i (e i path)
    unit i := (e i).sum_comp (lp.zeroNodeLP.flow i) |>.trans (lp.zeroNodeLP.unit i)
    capacity := ?_
    source_buying := lp.source_buying
    source_physical _ := rfl
    target_buying := ?_
    target_physical _ := rfl }
  · intro i v
    have sumEq := (e i).sum_comp (fun path => if v ∈ path.val.support then lp.zeroNodeLP.flow i path else 0)
    have supports : ∀ path, (e i path).val.support = path.val.support :=
      fun path => castPath_support (zeroTarget_eq lp lengths metadata i).symm path
    simp_rw [supports] at sumEq
    by_cases hv : lp.physical v = 0
    · simpa only [restrictedOpening, if_pos hv] using sumEq.trans_le (zeroNodeLP_original_capacity lp i v)
    · rw [restrictedOpening, if_neg hv]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro path _
      have absent : v ∉ path.val.support := by
        intro member
        exact hv (zeroGraph_walk_nodes G lp.physical path.val (lp.source_physical i) v member)
      simp only [if_neg absent]
  · intro i
    rw [← zeroTarget_eq lp lengths metadata i]
    exact lp.zeroNodeLP.target_buying i

@[simp] theorem zeroMetadataLP_buyingBudget (lengths : Fin h → ℚ) (metadata : ∀ i, lengths i = lp.fractionalLength i) :
    (zeroMetadataLP lp lengths metadata).buyingBudget =
      restrictedBudget lp.buying lp.physical lp.opening := rfl

theorem restrictedBudget_le : restrictedBudget lp.buying lp.physical lp.opening ≤ lp.buyingBudget := by
  classical
  unfold restrictedBudget NodeLP.buyingBudget
  apply Finset.sum_le_sum
  intro v _
  by_cases hz : lp.physical v = 0
  · by_cases hb : lp.buying v = 0
    · simp [restrictedOpening, raisedOpening, hz, hb]
    · simp [restrictedOpening, raisedOpening, hz, hb]
  · simp only [restrictedOpening, if_neg hz, mul_zero]
    exact mul_nonneg (lp.buying_nonneg v) (lp.opening_bounds v).1

theorem restrictedBudget_nonneg : 0 ≤ restrictedBudget lp.buying lp.physical lp.opening := by
  classical
  unfold restrictedBudget
  apply Finset.sum_nonneg
  intro v _
  apply mul_nonneg (lp.buying_nonneg v)
  by_cases hz : lp.physical v = 0
  · simpa [restrictedOpening, hz] using (lp.opening_bounds v).1
  · simp [restrictedOpening, hz]

@[simp] theorem zeroMetadataLP_fractionalLength (lengths : Fin h → ℚ)
    (metadata : ∀ i, lengths i = lp.fractionalLength i) (i : Fin h) :
    (zeroMetadataLP lp lengths metadata).fractionalLength i = 0 := by
  classical
  simp [NodeLP.fractionalLength, zeroMetadataLP, NodeMetric.walkWeight]

end BuyAtBulk.Computation.Rounding
