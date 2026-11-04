import BuyAtBulk.UpperBound.FixedRows
import BuyAtBulk.UpperBound.BuyingCosts
import BuyAtBulk.UpperBound.EligibleEdges

/-! The source core begins by retaining its seed, buying the deterministic
fixed-row helper and every zero-buying node, and resetting records/auxiliary
edges. Only helper buying, never any seed buying, is charged to initialization. -/
noncomputable section
namespace BuyAtBulk.UpperBound.CoreRun

variable {V : Type} [Fintype V] {G : SimpleGraph V} {h : ℕ}
local instance coreInitializationDecEq : DecidableEq V := Classical.decEq V
local instance coreInitializationAdj : DecidableRel G.Adj := Classical.decRel _

variable (lp : NodeLP G h)

def zeroBuyingNodes : Finset V := Finset.univ.filter fun v => lp.buying v = 0

def initialState (allowance : Fin h → ℚ) (ratio : ℕ) (budget_pos : 0 < lp.buyingBudget)
    (ratio_ge : 2 ≤ ratio) (allowance_pos : ∀ i, 0 < allowance i)
    (length_bound : ∀ i, lp.fractionalLength i ≤ allowance i / 64) (seed : Finset V) : RoundingState G where
  bought := seed ∪ (lp.fixedTollData allowance ratio budget_pos ratio_ge allowance_pos length_bound).helperSet h ∪ zeroBuyingNodes lp
  centers := []
  edges := []

theorem initial_seed_bought (allowance : Fin h → ℚ) (ratio : ℕ) (budget_pos : 0 < lp.buyingBudget)
    (ratio_ge : 2 ≤ ratio) (allowance_pos : ∀ i, 0 < allowance i)
    (length_bound : ∀ i, lp.fractionalLength i ≤ allowance i / 64) (seed : Finset V) :
    seed ⊆ (initialState lp allowance ratio budget_pos ratio_ge allowance_pos length_bound seed).bought :=
  Finset.subset_union_left.trans Finset.subset_union_left

theorem initial_helper_bought (allowance : Fin h → ℚ) (ratio : ℕ) (budget_pos : 0 < lp.buyingBudget)
    (ratio_ge : 2 ≤ ratio) (allowance_pos : ∀ i, 0 < allowance i)
    (length_bound : ∀ i, lp.fractionalLength i ≤ allowance i / 64) (seed : Finset V) :
    (lp.fixedTollData allowance ratio budget_pos ratio_ge allowance_pos length_bound).helperSet h ⊆
      (initialState lp allowance ratio budget_pos ratio_ge allowance_pos length_bound seed).bought :=
  Finset.subset_union_right.trans Finset.subset_union_left

theorem initial_zero_bought (allowance : Fin h → ℚ) (ratio : ℕ) (budget_pos : 0 < lp.buyingBudget)
    (ratio_ge : 2 ≤ ratio) (allowance_pos : ∀ i, 0 < allowance i)
    (length_bound : ∀ i, lp.fractionalLength i ≤ allowance i / 64) (seed : Finset V)
    (v : V) (zero : lp.buying v = 0) :
    v ∈ (initialState lp allowance ratio budget_pos ratio_ge allowance_pos length_bound seed).bought := by
  apply Finset.mem_union_right
  simp [zeroBuyingNodes, zero]

theorem initial_edges_eligible (allowance : Fin h → ℚ) (ratio : ℕ) (budget_pos : 0 < lp.buyingBudget)
    (ratio_ge : 2 ≤ ratio) (allowance_pos : ∀ i, 0 < allowance i)
    (length_bound : ∀ i, lp.fractionalLength i ≤ allowance i / 64) (seed : Finset V) :
    EdgesEligible G (initialState lp allowance ratio budget_pos ratio_ge allowance_pos length_bound seed) := by
  simp [EdgesEligible, initialState]

theorem nodeBuying_eq_sum (buying : V → ℚ) (nodes : Finset V) :
    nodeBuying buying nodes = ∑ v ∈ nodes, buying v := by
  unfold nodeBuying
  rw [← Finset.sum_filter]
  congr 1
  ext v
  simp

theorem union_zero_buying_le (buying : V → ℚ) (nonneg : ∀ v, 0 ≤ buying v) (seed helper : Finset V) :
    nodeBuying buying (seed ∪ helper ∪ (Finset.univ.filter fun v => buying v = 0)) ≤
      nodeBuying buying seed + nodeBuying buying helper := by
  unfold nodeBuying
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v _
  by_cases hs : v ∈ seed <;> by_cases hh : v ∈ helper <;> by_cases hz : buying v = 0 <;>
    simp [hs, hh, hz] <;> linarith [nonneg v]

theorem initial_buying_charge (allowance : Fin h → ℚ) (ratio : ℕ) (budget_pos : 0 < lp.buyingBudget)
    (hh : 0 < h) (ratio_ge : 2 ≤ ratio) (allowance_pos : ∀ i, 0 < allowance i)
    (length_bound : ∀ i, lp.fractionalLength i ≤ allowance i / 64) (seed : Finset V) :
    nodeBuying lp.buying (initialState lp allowance ratio budget_pos ratio_ge allowance_pos length_bound seed).bought -
      nodeBuying lp.buying seed < 4 * Helper.TollData.alpha h * lp.buyingBudget := by
  let D := lp.fixedTollData allowance ratio budget_pos ratio_ge allowance_pos length_bound
  have helper_cost : nodeBuying lp.buying (D.helperSet h) < 4 * Helper.TollData.alpha h * lp.buyingBudget := by
    rw [nodeBuying_eq_sum]
    exact D.helper_cost_lt h hh budget_pos (lp.fixedRow_card_bound allowance ratio hh ratio_ge)
  have initial_le := union_zero_buying_le lp.buying lp.buying_nonneg seed (D.helperSet h)
  change nodeBuying lp.buying (seed ∪ D.helperSet h ∪ zeroBuyingNodes lp) - nodeBuying lp.buying seed < _
  change nodeBuying lp.buying (seed ∪ D.helperSet h ∪ zeroBuyingNodes lp) ≤ _ at initial_le
  linarith

end BuyAtBulk.UpperBound.CoreRun
