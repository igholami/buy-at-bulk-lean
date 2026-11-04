import BuyAtBulk.Computation.Core.Algorithm
import BuyAtBulk.Computation.Core.HelperRefinement
import BuyAtBulk.Computation.Batch.Rental
import BuyAtBulk.UpperBound.CoreRun.Initialization
import BuyAtBulk.UpperBound.CoreFactors
import BuyAtBulk.UpperBound.AuxiliaryBuyingBound

/-! Numerical correctness of the actual complete core program, including its
materialized rows, explicit helper schedules and stored output routes. -/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.Computation.Core
open BuyAtBulk.UpperBound
variable {V : Type} [Fintype V] [vertexDecEq : DecidableEq V] {n h : ℕ} {G : SimpleGraph V} [DecidableRel G.Adj]
    (numbering : V ≃ Fin n) (lp : NodeLP G h)

theorem core_correct (allowance : Fin h → ℚ) (active : Finset (Fin h)) (ratio r : ℕ)
    (budget_pos : 0 < lp.buyingBudget) (hh : 0 < h) (ratio_ge : 8 ≤ ratio) (r_ge : 1 ≤ r)
    (allowance_pos : ∀ i, 0 < allowance i) (length_bound : ∀ i, lp.fractionalLength i ≤ allowance i / 64)
    (seed : Finset V) :
    ∃ after entries,
      run G numbering lp.buying lp.physical lp.opening lp.buyingBudget allowance lp.source lp.target active ratio r seed =
        some (after, entries) ∧
      RunExec G lp.buying lp.physical lp.buyingBudget ratio (6 * (r : ℚ) + 6) lp.source lp.target allowance
        (CoreRun.requestOrder active allowance) (initialState G numbering lp.buying lp.opening lp.buyingBudget
          (lpDatabase numbering lp allowance ratio) seed) after ∧
      seed ⊆ after.bought ∧
      (nodeBuying lp.buying after.bought : ℝ) ≤ (nodeBuying lp.buying seed : ℝ) +
        coreBuyingFactor h ratio r * lp.buyingBudget ∧
      entries.map (fun entry => entry.1) = CoreRun.requestOrder active allowance ∧
      (∀ entry ∈ entries, entry.2.val.support.toFinset ⊆ after.bought ∧
        NodeMetric.walkWeight G lp.physical entry.2.val ≤ coreRouteFactor h ratio r * allowance entry.1) ∧
      ∀ i ∈ active, ∃ path : G.Path (lp.source i) (lp.target i),
        ⟨i, path⟩ ∈ entries ∧ path.val.support.toFinset ⊆ after.bought := by
  have canonical_decider : vertexDecEq = Classical.decEq V := Subsingleton.elim _ _
  cases canonical_decider
  letI : DecidableEq V := Classical.decEq V
  have ratio_ge' : 2 ≤ ratio := by omega
  let initial := initialState G numbering lp.buying lp.opening lp.buyingBudget (lpDatabase numbering lp allowance ratio) seed
  let selection := computedSelection numbering lp allowance ratio budget_pos ratio_ge' allowance_pos length_bound hh
  let thresholdFactor : ℚ := 6 * (r : ℚ) + 6
  have top : ∀ (state : RoundingState G) i,
      NodeMetric.distance G (mixedNodeWeight G lp.buying lp.physical state (allowance i)
        (gridScale lp.buyingBudget ratio 0)) (lp.source i) (lp.target i) (lp.reachable i) <
        gridScale lp.buyingBudget ratio 0 := by
    intro state i
    simpa only [gridScale, pow_zero, div_one] using
      lp.graph_top_scale_ineligible i state (allowance i) budget_pos (allowance_pos i) (length_bound i)
  obtain ⟨after, entries, computed, execution, indices, supported, every⟩ :=
    Batch.batch_correct G numbering lp.buying lp.physical lp.buying_nonneg lp.physical_nonneg lp.buyingBudget ratio
      thresholdFactor lp.source lp.target allowance lp.reachable budget_pos.le allowance_pos hh ratio_ge' top
      (CoreRun.requestOrder active allowance) initial
  have retained : seed ⊆ initial.bought := Finset.subset_union_left.trans Finset.subset_union_left
  have helper_bought : selection.nodes ⊆ initial.bought := Finset.subset_union_right.trans Finset.subset_union_left
  have zero_bought : ∀ v, lp.buying v = 0 → v ∈ initial.bought := by
    intro v zero
    apply Finset.mem_union_right
    exact (mem_zeroBuyingNodes numbering lp.buying v).mpr zero
  have buying := lp.run_buying_bound allowance ratio r budget_pos hh ratio_ge' r_ge allowance_pos length_bound selection
    execution (CoreRun.requestOrder_sorted active allowance) (CoreRun.requestOrder_nodup active allowance)
    rfl rfl helper_bought zero_bought
  have helper_cost : nodeBuying lp.buying selection.nodes < 4 * Helper.TollData.alpha h * lp.buyingBudget := by
    rw [CoreRun.nodeBuying_eq_sum]
    exact selection.buying_lt
  have zero_set : zeroBuyingNodes numbering lp.buying = Finset.univ.filter fun v => lp.buying v = 0 := by
    ext v
    simp only [mem_zeroBuyingNodes, Finset.mem_filter, Finset.mem_univ, true_and]
  have initialization : nodeBuying lp.buying initial.bought - nodeBuying lp.buying seed <
      4 * Helper.TollData.alpha h * lp.buyingBudget := by
    have union_bound := CoreRun.union_zero_buying_le lp.buying lp.buying_nonneg seed selection.nodes
    change nodeBuying lp.buying (seed ∪ selection.nodes ∪ zeroBuyingNodes numbering lp.buying) -
      nodeBuying lp.buying seed < _
    rw [zero_set]
    linarith
  have initialization_real : (nodeBuying lp.buying initial.bought : ℝ) - (nodeBuying lp.buying seed : ℝ) ≤
      4 * (Helper.TollData.alpha h : ℝ) * lp.buyingBudget := by
    have cast : ((nodeBuying lp.buying initial.bought - nodeBuying lp.buying seed : ℚ) : ℝ) ≤
        ((4 * Helper.TollData.alpha h * lp.buyingBudget : ℚ) : ℝ) := by exact_mod_cast initialization.le
    push_cast at cast
    exact cast
  have threshold_ge : 1 ≤ thresholdFactor := by
    dsimp [thresholdFactor]
    have nonneg : (0 : ℚ) ≤ r := Nat.cast_nonneg _
    linarith
  have rental := Batch.entries_rental G numbering lp.buying lp.physical lp.buying_nonneg lp.physical_nonneg
    lp.buyingBudget ratio thresholdFactor lp.source lp.target allowance lp.reachable budget_pos allowance_pos hh ratio_ge'
    threshold_ge lp.source_buying lp.target_buying lp.source_physical lp.target_physical top
    (CoreRun.requestOrder active allowance) initial after entries computed
  refine ⟨after, entries, computed, execution, retained.trans (RunExec.bought_mono G execution), ?_, indices, ?_, ?_⟩
  · simp only [addedBuying, Rat.cast_sub] at buying
    unfold coreBuyingFactor
    nlinarith
  · intro entry member
    refine ⟨supported entry member, (rental entry member).trans_eq ?_⟩
    dsimp [thresholdFactor, coreRouteFactor]
    ring
  · intro i member
    exact every i ((CoreRun.mem_requestOrder active allowance i).mpr member)

end BuyAtBulk.Computation.Core


/-! Public actual-output core rounding theorem. The output is the result of
one deterministic program on supplied numbered graph and numeric LP data. -/
namespace BuyAtBulk.Computation.Core
open BuyAtBulk.UpperBound
variable {V : Type} [Fintype V] [DecidableEq V] {n h : ℕ} {G : SimpleGraph V} [DecidableRel G.Adj]
    (numbering : V ≃ Fin n) (lp : NodeLP G h)

theorem core_rounding_correct (allowance : Fin h → ℚ) (active : Finset (Fin h)) (ratio r : ℕ)
    (budget_pos : 0 < lp.buyingBudget) (hh : 0 < h) (ratio_ge : 8 ≤ ratio) (r_ge : 1 ≤ r)
    (allowance_pos : ∀ i, 0 < allowance i) (length_bound : ∀ i, lp.fractionalLength i ≤ allowance i / 64)
    (seed : Finset V) :
    ∃ after entries,
      run G numbering lp.buying lp.physical lp.opening lp.buyingBudget allowance lp.source lp.target active ratio r seed =
        some (after, entries) ∧
      RunExec G lp.buying lp.physical lp.buyingBudget ratio (6 * (r : ℚ) + 6) lp.source lp.target allowance
        (CoreRun.requestOrder active allowance) (initialState G numbering lp.buying lp.opening lp.buyingBudget
          (lpDatabase numbering lp allowance ratio) seed) after ∧
      seed ⊆ after.bought ∧
      (nodeBuying lp.buying after.bought : ℝ) ≤ (nodeBuying lp.buying seed : ℝ) +
        coreBuyingFactor h ratio r * lp.buyingBudget ∧
      entries.map (fun entry => entry.1) = CoreRun.requestOrder active allowance ∧
      ∀ i ∈ active, ∃ path : G.Path (lp.source i) (lp.target i),
        ⟨i, path⟩ ∈ entries ∧ path.val.support.toFinset ⊆ after.bought ∧
        NodeMetric.walkWeight G lp.physical path.val ≤ coreRouteFactor h ratio r * allowance i := by
  obtain ⟨after, entries, computed, execution, retained, buying, indices, bounds, every⟩ :=
    core_correct numbering lp allowance active ratio r budget_pos hh ratio_ge r_ge allowance_pos length_bound seed
  refine ⟨after, entries, computed, execution, retained, buying, indices, ?_⟩
  intro i member
  obtain ⟨path, stored, supported⟩ := every i member
  exact ⟨path, stored, supported, (bounds ⟨i, path⟩ stored).2⟩

end BuyAtBulk.Computation.Core
