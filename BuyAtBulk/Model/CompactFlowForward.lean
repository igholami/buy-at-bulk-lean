import BuyAtBulk.Model.CompactFlowPath

/-! The exact path-flow to compact node-split flow transformation. -/
noncomputable section
namespace BuyAtBulk.UpperBound.NodeLP
open BuyAtBulk.CompactFlow
variable {V : Type} [Fintype V] {G : SimpleGraph V} {h : ℕ}
local instance compactFlowForwardDecEq : DecidableEq V := Classical.decEq _
local instance compactFlowForwardDecRel : DecidableRel G.Adj := Classical.decRel _
variable (lp : UpperBound.NodeLP G h)

def compactNode (i : Fin h) (v : V) : ℚ :=
  ∑ p, lp.flow i p * nodeVisits p.val v

def compactTransport (i : Fin h) (u v : V) : ℚ :=
  ∑ p, lp.flow i p * transportVisits p.val u v

theorem compactNode_eq (i : Fin h) (v : V) :
    lp.compactNode i v = ∑ p, if v ∈ p.val.support then lp.flow i p else 0 := by
  simp only [compactNode, nodeVisits_path]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp

theorem compact_incoming_balance (i : Fin h) (v : V) :
    lp.compactNode i v - (∑ u, lp.compactTransport i u v) =
      if lp.source i = v then 1 else 0 := by
  simp only [compactNode, compactTransport]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  have heq : ∀ p : G.Path (lp.source i) (lp.target i),
      lp.flow i p * nodeVisits p.val v - ∑ u, lp.flow i p * transportVisits p.val u v =
      lp.flow i p * (if lp.source i = v then 1 else 0) := by
    intro p
    rw [← Finset.mul_sum, visits_incoming]
    ring
  simp_rw [heq]
  rw [← Finset.sum_mul, lp.unit, one_mul]

theorem compact_outgoing_balance (i : Fin h) (v : V) :
    (∑ u, lp.compactTransport i v u) - lp.compactNode i v =
      -(if lp.target i = v then 1 else 0) := by
  simp only [compactNode, compactTransport]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  have heq : ∀ p : G.Path (lp.source i) (lp.target i),
      (∑ u, lp.flow i p * transportVisits p.val v u) - lp.flow i p * nodeVisits p.val v =
      lp.flow i p * -(if lp.target i = v then 1 else 0) := by
    intro p
    rw [← Finset.mul_sum, visits_outgoing]
    ring
  simp_rw [heq]
  rw [← Finset.sum_mul, lp.unit, one_mul]

/-- The compact flow induced by a feasible typed all-simple-path LP. -/
def toCompact : CompactFlow.Solution G h where
  source := lp.source
  target := lp.target
  buying := lp.buying
  physical := lp.physical
  demand := lp.demand
  opening := lp.opening
  node := lp.compactNode
  transport := lp.compactTransport
  buying_nonneg := lp.buying_nonneg
  physical_nonneg := lp.physical_nonneg
  demand_pos := lp.demand_pos
  opening_bounds := lp.opening_bounds
  node_nonneg := fun i v => Finset.sum_nonneg fun p _ =>
    mul_nonneg (lp.flow_nonneg i p) (Nat.cast_nonneg _)
  transport_nonneg := fun i u v => Finset.sum_nonneg fun p _ =>
    mul_nonneg (lp.flow_nonneg i p) (transportVisits_nonneg p.val u v)
  transport_nonedge := by
    intro i u v huv
    simp only [compactTransport, transportVisits_nonedge _ u v huv, mul_zero,
      Finset.sum_const_zero]
  capacity := by intro i v; rw [lp.compactNode_eq]; exact lp.capacity i v
  incoming_balance := lp.compact_incoming_balance
  outgoing_balance := lp.compact_outgoing_balance
  source_buying := lp.source_buying
  source_physical := lp.source_physical
  target_buying := lp.target_buying
  target_physical := lp.target_physical

@[simp] theorem toCompact_buyingBudget : lp.toCompact.buyingBudget = lp.buyingBudget := rfl

theorem toCompact_fractionalLength (i : Fin h) :
    lp.toCompact.fractionalLength i = lp.fractionalLength i := by
  classical
  simp only [CompactFlow.Solution.fractionalLength, toCompact, compactNode,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  simp only [nodeVisits_path, NodeMetric.walkWeight]
  rw [Finset.sum_mul]
  calc
    ∑ v, lp.physical v * (lp.flow i p * if v ∈ p.val.support then 1 else 0) =
        ∑ v ∈ p.val.support.toFinset, lp.physical v * lp.flow i p := by
      simp only [mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext v; simp
      · intro v _; rfl
    _ = _ := rfl

@[simp] theorem toCompact_rentalBudget : lp.toCompact.rentalBudget = lp.rentalBudget := by
  unfold CompactFlow.Solution.rentalBudget rentalBudget
  simp_rw [lp.toCompact_fractionalLength]
  rfl

end BuyAtBulk.UpperBound.NodeLP
