import BuyAtBulk.UpperBound.ZeroLengthFlow

/-! Feasible all-node zero-length preprocessing with the original request
normalizer h and original B. Positive-rental requests become free self-pairs;
zero-rental commodities retain all their actual zero-node paths. -/
noncomputable section
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V]
local instance zeroLengthLPLocalInst1 : DecidableEq V := Classical.decEq V
local instance zeroLengthLPLocalInst2 (H : SimpleGraph V) : DecidableRel H.Adj := Classical.decRel _

structure FreeCommodity (H : SimpleGraph V) (buying opening : V → ℚ) (source : V) where
  target : V
  flow : H.Path source target → ℚ
  flow_nonneg : ∀ path, 0 ≤ flow path
  unit : ∑ path, flow path = 1
  capacity : ∀ v, (∑ path, if v ∈ path.val.support then flow path else 0) ≤ opening v
  target_buying : buying target = 0

namespace NodeLP

variable {G : SimpleGraph V} {h : ℕ} (lp : NodeLP G h)

def zeroCommodity (i : Fin h) :
    FreeCommodity (zeroGraph G lp.physical) lp.buying lp.raisedOpening (lp.source i) := by
  classical
  by_cases zero : lp.fractionalLength i = 0
  · exact {
      target := lp.target i
      flow := lp.zeroFlow i zero
      flow_nonneg := lp.zeroFlow_nonneg i zero
      unit := lp.zeroFlow_unit i zero
      capacity := fun v => (lp.zeroFlow_resource i zero v).trans_le
        ((lp.capacity i v).trans (lp.opening_le_raised v))
      target_buying := lp.target_buying i }
  · let nil : (zeroGraph G lp.physical).Path (lp.source i) (lp.source i) := SimpleGraph.Path.nil
    refine {
      target := lp.source i
      flow := fun path => if path = nil then 1 else 0
      flow_nonneg := ?_
      unit := ?_
      capacity := ?_
      target_buying := lp.source_buying i }
    · intro path
      split_ifs <;> norm_num
    · rw [Finset.sum_eq_single nil]
      · simp
      · intro path _ hne
        simp [hne]
      · simp
    · intro v
      have single : (∑ path : (zeroGraph G lp.physical).Path (lp.source i) (lp.source i),
          if v ∈ path.val.support then (if path = nil then (1 : ℚ) else 0) else 0) =
          if v = lp.source i then 1 else 0 := by
        rw [Finset.sum_eq_single nil]
        · simp [nil, SimpleGraph.Path.nil]
        · intro path _ hne
          simp [hne]
        · simp
      rw [single]
      by_cases hv : v = lp.source i
      · subst v
        simp [raisedOpening, lp.source_buying]
      · simp only [if_neg hv]
        exact (lp.raisedOpening_bounds v).1

def zeroNodeLP : NodeLP (zeroGraph G lp.physical) h where
  source := lp.source
  target i := (lp.zeroCommodity i).target
  buying := lp.buying
  physical := fun _ => 0
  demand := lp.demand
  opening := lp.raisedOpening
  flow i := (lp.zeroCommodity i).flow
  buying_nonneg := lp.buying_nonneg
  physical_nonneg _ := le_rfl
  demand_pos := lp.demand_pos
  opening_bounds := lp.raisedOpening_bounds
  flow_nonneg i := (lp.zeroCommodity i).flow_nonneg
  unit i := (lp.zeroCommodity i).unit
  capacity i := (lp.zeroCommodity i).capacity
  source_buying := lp.source_buying
  source_physical _ := rfl
  target_buying i := (lp.zeroCommodity i).target_buying
  target_physical _ := rfl

@[simp] theorem zeroNodeLP_buyingBudget : lp.zeroNodeLP.buyingBudget = lp.buyingBudget :=
  lp.raisedOpening_buyingBudget

@[simp] theorem zeroNodeLP_fractionalLength (i : Fin h) : lp.zeroNodeLP.fractionalLength i = 0 := by
  simp [fractionalLength, zeroNodeLP, NodeMetric.walkWeight]

@[simp] theorem zeroNodeLP_rentalBudget : lp.zeroNodeLP.rentalBudget = 0 := by
  simp [rentalBudget]

theorem zeroNodeLP_target_active (i : Fin h) (zero : lp.fractionalLength i = 0) :
    lp.zeroNodeLP.target i = lp.target i := by
  simp only [zeroNodeLP, zeroCommodity, dif_pos zero]

/-- Actual bought routes for active zero-length commodities project back to
original graph routes of physical length exactly zero. -/
theorem project_zero_bought_route (i : Fin h) (zero : lp.fractionalLength i = 0) (bought : Finset V)
    (supported : ∃ path : (zeroGraph G lp.physical).Path (lp.zeroNodeLP.source i) (lp.zeroNodeLP.target i),
      path.val.support.toFinset ⊆ bought) :
    ∃ path : G.Path (lp.source i) (lp.target i),
      path.val.support.toFinset ⊆ bought ∧ NodeMetric.walkWeight G lp.physical path.val = 0 := by
  change ∃ path : (zeroGraph G lp.physical).Path (lp.source i) (lp.zeroNodeLP.target i),
    path.val.support.toFinset ⊆ bought at supported
  rw [lp.zeroNodeLP_target_active i zero] at supported
  obtain ⟨path, member⟩ := supported
  refine ⟨projectZeroPath G lp.physical path, ?_, ?_⟩
  · simpa only [projectZeroPath_support] using member
  · exact projectZeroPath_physical_zero G lp.physical path (lp.source_physical i)

end NodeLP
end BuyAtBulk.UpperBound
