import BuyAtBulk.Computation.Rounding.MetadataLP

/-! Inactive request slots are free self-pairs. They contribute no helper rows,
while the original request count remains the grid/helper normalizer. -/
noncomputable section
namespace BuyAtBulk.Computation.Rounding
open BuyAtBulk.UpperBound
variable {V : Type} [Fintype V] {G : SimpleGraph V} {h : ℕ} (lp : NodeLP G h)
local instance : DecidableEq V := Classical.decEq V
local instance : DecidableRel G.Adj := Classical.decRel _

private theorem castPath_eq_copy {s t t' : V} (eq : t' = t) (path : G.Path s t') :
    Equiv.cast (congrArg (fun v => G.Path s v) eq) path = ShortestPath.copyPath path rfl eq := by
  cases eq
  rfl

private theorem source_opening (i : Fin h) : lp.opening (lp.source i) = 1 := by
  classical
  have bound := lp.capacity i (lp.source i)
  have member (path : G.Path (lp.source i) (lp.target i)) : lp.source i ∈ path.val.support :=
    path.val.start_mem_support
  simp only [member, ite_true, lp.unit] at bound
  exact le_antisymm (lp.opening_bounds _).2 bound

def positiveNil (lengths : Fin h → ℚ) (i : Fin h) (zero : lengths i = 0) :
    G.Path (lp.source i) (positiveTarget lp.source lp.target lengths i) :=
  ShortestPath.copyPath SimpleGraph.Path.nil rfl (by simp [positiveTarget, zero])

def positivePath (lengths : Fin h → ℚ) (i : Fin h) (positive : lengths i ≠ 0)
    (path : G.Path (lp.source i) (positiveTarget lp.source lp.target lengths i)) :
    G.Path (lp.source i) (lp.target i) :=
  ShortestPath.copyPath path rfl (by simp [positiveTarget, positive])

def positiveFlow (lengths : Fin h → ℚ) (i : Fin h)
    (path : G.Path (lp.source i) (positiveTarget lp.source lp.target lengths i)) : ℚ :=
  if zero : lengths i = 0 then (if path = positiveNil lp lengths i zero then 1 else 0)
  else lp.flow i (positivePath lp lengths i zero path)

private def positiveEquiv (lengths : Fin h → ℚ) (i : Fin h) (positive : lengths i ≠ 0) :
    G.Path (lp.source i) (positiveTarget lp.source lp.target lengths i) ≃ G.Path (lp.source i) (lp.target i) :=
  Equiv.cast (congrArg (fun v => G.Path (lp.source i) v) (by simp [positiveTarget, positive]))

private theorem positiveEquiv_apply (lengths : Fin h → ℚ) (i : Fin h) (positive : lengths i ≠ 0)
    (path : G.Path (lp.source i) (positiveTarget lp.source lp.target lengths i)) :
    positiveEquiv lp lengths i positive path = positivePath lp lengths i positive path := by
  exact castPath_eq_copy _ _

private theorem positivePath_support (lengths : Fin h → ℚ) (i : Fin h) (positive : lengths i ≠ 0)
    (path : G.Path (lp.source i) (positiveTarget lp.source lp.target lengths i)) :
    (positivePath lp lengths i positive path).val.support = path.val.support := by
  simp [positivePath, ShortestPath.copyPath]

private theorem positiveFlow_capacity (lengths : Fin h → ℚ) (i : Fin h) (v : V) :
    (∑ path, if v ∈ path.val.support then positiveFlow lp lengths i path else 0) ≤ lp.opening v := by
  classical
  by_cases zero : lengths i = 0
  · simp only [positiveFlow, dif_pos zero]
    rw [Finset.sum_eq_single (positiveNil lp lengths i zero)]
    · simp only [ite_true, positiveNil, ShortestPath.copyPath, SimpleGraph.Walk.support_copy,
        SimpleGraph.Path.nil, SimpleGraph.Walk.support_nil, List.mem_singleton]
      by_cases same : v = lp.source i
      · subst v
        simp [source_opening]
      · simp [same, (lp.opening_bounds v).1]
    · intro path _ ne
      simp [ne]
    · simp
  · have transported := (positiveEquiv lp lengths i zero).sum_comp
      (fun path => if v ∈ path.val.support then lp.flow i path else 0)
    simp only [positiveEquiv_apply, positivePath_support] at transported
    simpa only [positiveFlow, dif_neg zero] using transported.trans_le (lp.capacity i v)

def positiveMetadataLP (lengths : Fin h → ℚ) : NodeLP G h := by
  classical
  exact {
    source := lp.source
    target := positiveTarget lp.source lp.target lengths
    buying := lp.buying
    physical := lp.physical
    demand := lp.demand
    opening := lp.opening
    flow := positiveFlow lp lengths
    buying_nonneg := lp.buying_nonneg
    physical_nonneg := lp.physical_nonneg
    demand_pos := lp.demand_pos
    opening_bounds := lp.opening_bounds
    flow_nonneg := by
      intro i path
      by_cases zero : lengths i = 0
      · simp only [positiveFlow, dif_pos zero]
        split_ifs <;> norm_num
      · simpa only [positiveFlow, dif_neg zero] using lp.flow_nonneg i (positivePath lp lengths i zero path)
    unit := by
      intro i
      by_cases zero : lengths i = 0
      · simp [positiveFlow, zero]
      · simpa only [positiveFlow, dif_neg zero, positiveEquiv_apply] using
          ((positiveEquiv lp lengths i zero).sum_comp (lp.flow i)).trans (lp.unit i)
    capacity := positiveFlow_capacity lp lengths
    source_buying := lp.source_buying
    source_physical := lp.source_physical
    target_buying := by intro i; unfold positiveTarget; split_ifs <;> simp [lp.source_buying, lp.target_buying]
    target_physical := by intro i; unfold positiveTarget; split_ifs <;> simp [lp.source_physical, lp.target_physical] }

@[simp] theorem positiveMetadataLP_buyingBudget (lengths : Fin h → ℚ) :
    (positiveMetadataLP lp lengths).buyingBudget = lp.buyingBudget := rfl

theorem positiveMetadataLP_fractionalLength (lengths : Fin h → ℚ) (i : Fin h) :
    (positiveMetadataLP lp lengths).fractionalLength i = if lengths i = 0 then 0 else lp.fractionalLength i := by
  classical
  unfold NodeLP.fractionalLength
  change (∑ path, NodeMetric.walkWeight G lp.physical path.val * positiveFlow lp lengths i path) = _
  by_cases zero : lengths i = 0
  · simp only [if_pos zero, positiveFlow, dif_pos zero]
    rw [Finset.sum_eq_single (positiveNil lp lengths i zero)]
    · simp [positiveNil, ShortestPath.copyPath, NodeMetric.walkWeight, lp.source_physical]
    · intro path _ ne
      simp [ne]
    · simp
  · rw [if_neg zero]
    have transported := (positiveEquiv lp lengths i zero).sum_comp
      (fun path => NodeMetric.walkWeight G lp.physical path.val * lp.flow i path)
    simpa only [positiveFlow, dif_neg zero, positiveEquiv_apply, positivePath,
      ShortestPath.copyPath_weight] using transported

end BuyAtBulk.Computation.Rounding
