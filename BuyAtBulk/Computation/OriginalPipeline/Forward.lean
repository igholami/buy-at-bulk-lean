import BuyAtBulk.Computation.FlowDecomposition.Lift

/-! Executable sparse-list forward compact-flow construction. -/
set_option maxHeartbeats 1800000
namespace BuyAtBulk.Computation.OriginalPipeline
open BuyAtBulk.CompactFlow
theorem univ_independent {P : Type} (a b : Fintype P) :
    @Finset.univ P a = @Finset.univ P b := by rw [Subsingleton.elim a b]

section Forward
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {h : ℕ}
    (lp : UpperBound.NodeLP G h)
    (entries : ∀ i, FlowDecomposition.WeightedPaths G (lp.source i) (lp.target i))
    (agrees : ∀ i p, lp.flow i p = FlowDecomposition.listFlow G (entries i) p)

def forwardNode (i : Fin h) (v : V) : ℚ :=
  ((entries i).map fun entry => if v ∈ entry.2.val.support then entry.1 else 0).sum

def forwardArc (i : Fin h) (u v : V) : ℚ :=
  ((entries i).map fun entry => if FlowDecomposition.usesArc G entry.2 u v then entry.1 else 0).sum

include agrees in
theorem forwardNode_eq (i : Fin h) (v : V) :
    forwardNode lp entries i v = lp.compactNode i v := by
  classical
  rw [lp.compactNode_eq]
  have weighted := FlowDecomposition.weighted_listFlow G (entries i)
    (fun p => if v ∈ p.val.support then (1 : ℚ) else 0)
  simp only [mul_ite, mul_one, mul_zero] at weighted
  rw [forwardNode, ← weighted]
  apply Finset.sum_congr (univ_independent _ _)
  intro p _
  rw [agrees]
  split_ifs <;> rfl

include agrees in
theorem forwardArc_eq (i : Fin h) (u v : V) :
    forwardArc lp entries i u v = lp.compactTransport i u v := by
  classical
  unfold UpperBound.NodeLP.compactTransport
  have weighted := FlowDecomposition.weighted_listFlow G (entries i)
    (fun p => transportVisits p.val u v)
  have listed : forwardArc lp entries i u v =
      ((entries i).map fun entry => entry.1 * transportVisits entry.2.val u v).sum := by
    unfold forwardArc
    apply congrArg List.sum
    apply List.map_congr_left
    intro entry _
    rw [FlowDecomposition.visits_eq_usesArc]
    split <;> simp_all
  rw [listed, ← weighted]
  apply Finset.sum_congr (univ_independent _ _)
  intro p _
  rw [agrees]

/-- Materialize compact flows from the stored sparse list; the exponential
path type is used only by the correctness proof. -/
def forward : CompactFlow.Solution G h where
  source := lp.source
  target := lp.target
  buying := lp.buying
  physical := lp.physical
  demand := lp.demand
  opening := lp.opening
  node := forwardNode lp entries
  transport := forwardArc lp entries
  buying_nonneg := lp.buying_nonneg
  physical_nonneg := lp.physical_nonneg
  demand_pos := lp.demand_pos
  opening_bounds := lp.opening_bounds
  node_nonneg := by intro i v; rw [forwardNode_eq lp entries agrees]; exact lp.toCompact.node_nonneg i v
  transport_nonneg := by intro i u v; rw [forwardArc_eq lp entries agrees]; exact lp.toCompact.transport_nonneg i u v
  transport_nonedge := by intro i u v edge; rw [forwardArc_eq lp entries agrees]; exact lp.toCompact.transport_nonedge i u v edge
  capacity := by intro i v; rw [forwardNode_eq lp entries agrees]; exact lp.toCompact.capacity i v
  incoming_balance := by
    intro i v
    simp only [forwardNode_eq lp entries agrees, forwardArc_eq lp entries agrees]
    exact lp.toCompact.incoming_balance i v
  outgoing_balance := by
    intro i v
    simp only [forwardNode_eq lp entries agrees, forwardArc_eq lp entries agrees]
    exact lp.toCompact.outgoing_balance i v
  source_buying := lp.source_buying
  source_physical := lp.source_physical
  target_buying := lp.target_buying
  target_physical := lp.target_physical

@[simp] theorem forward_buying :
    (forward lp entries agrees).buyingBudget = lp.buyingBudget := rfl

theorem forward_length (i : Fin h) :
    (forward lp entries agrees).fractionalLength i = lp.fractionalLength i := by
  rw [← lp.toCompact_fractionalLength i]
  unfold CompactFlow.Solution.fractionalLength
  apply Finset.sum_congr rfl
  intro v _
  rw [show (forward lp entries agrees).node i v = lp.toCompact.node i v from forwardNode_eq lp entries agrees i v]
  rfl
end Forward
end BuyAtBulk.Computation.OriginalPipeline
