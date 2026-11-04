import BuyAtBulk.Model.CompactFlowDecomposition
import BuyAtBulk.Model.CompactFlowForward

/-! Compact flow to feasible rational simple-path flow. Residual directed
circulations are discarded; openings and buying cost are preserved, while
resource marginals and rental cost can only decrease. -/
noncomputable section
namespace BuyAtBulk.CompactFlow
variable {V : Type} [Fintype V] {G : SimpleGraph V} {h : ℕ}
local instance compactFlowReverseDecEq : DecidableEq V := Classical.decEq _
local instance compactFlowReverseDecRel : DecidableRel G.Adj := Classical.decRel _

/-- Resource throughput bound derived from incoming directed-arc bounds and
unit path mass, including the source split arc. -/
theorem node_marginal_le {s t : V} (w : G.Path s t → ℚ) (f : V → V → ℚ)
    (mass : ℚ) (hsum : ∑ p, w p = mass)
    (hcap : ∀ u v, (∑ p, w p * transportVisits p.val u v) ≤ f u v) (v : V) :
    (∑ p, w p * nodeVisits p.val v) ≤
      (∑ u, f u v) + mass * (if s = v then 1 else 0) := by
  calc
    (∑ p, w p * nodeVisits p.val v) =
        (∑ u, ∑ p, w p * transportVisits p.val u v) +
          mass * (if s = v then 1 else 0) := by
      simp_rw [visits_incoming, mul_add, Finset.mul_sum]
      rw [Finset.sum_add_distrib, Finset.sum_comm, ← Finset.sum_mul, hsum]
    _ ≤ _ := add_le_add (Finset.sum_le_sum fun u _ => hcap u v) le_rfl

namespace Solution
variable (f : Solution G h)

theorem exists_path_flow (i : Fin h) :
    ∃ w : G.Path (f.source i) (f.target i) → ℚ,
      (∀ p, 0 ≤ w p) ∧ (∑ p, w p = 1) ∧
      (∀ u v, (∑ p, w p * transportVisits p.val u v) ≤ f.transport i u v) ∧
      (pathSupport w).card ≤ (positiveArcs (f.transport i)).card + 1 := by
  apply decompose_transport (f.transport i) (f.source i) (f.target i) 1 (by norm_num)
    (f.transport_nonneg i) (f.transport_nonedge i)
  intro v
  have hi := f.incoming_balance i v
  have ho := f.outgoing_balance i v
  linarith

def pathFlow (i : Fin h) : G.Path (f.source i) (f.target i) → ℚ :=
  (f.exists_path_flow i).choose

theorem pathFlow_nonneg (i : Fin h) (p : G.Path (f.source i) (f.target i)) :
    0 ≤ f.pathFlow i p := (f.exists_path_flow i).choose_spec.1 p

theorem pathFlow_unit (i : Fin h) : ∑ p, f.pathFlow i p = 1 :=
  (f.exists_path_flow i).choose_spec.2.1

theorem pathFlow_arcs_le (i : Fin h) (u v : V) :
    (∑ p, f.pathFlow i p * transportVisits p.val u v) ≤ f.transport i u v :=
  (f.exists_path_flow i).choose_spec.2.2.1 u v

theorem pathFlow_support_bound (i : Fin h) :
    (pathSupport (f.pathFlow i)).card ≤ Fintype.card V ^ 2 + 1 := by
  apply (f.exists_path_flow i).choose_spec.2.2.2.trans
  apply Nat.add_le_add_right
  calc
    (positiveArcs (f.transport i)).card ≤ Fintype.card (V × V) := Finset.card_le_univ _
    _ = Fintype.card V ^ 2 := by simp [pow_two]

/-- The extracted path list has polynomially bounded support cardinality. This
is a mathematical size bound, not an implementation running-time bound. -/
theorem total_pathFlow_support_bound :
    (∑ i, (pathSupport (f.pathFlow i)).card) ≤ h * (Fintype.card V ^ 2 + 1) := by
  calc
    (∑ i, (pathSupport (f.pathFlow i)).card) ≤
        ∑ _i : Fin h, (Fintype.card V ^ 2 + 1) :=
      Finset.sum_le_sum fun i _ => f.pathFlow_support_bound i
    _ = _ := by simp

theorem pathFlow_nodes_le (i : Fin h) (v : V) :
    (∑ p, if v ∈ p.val.support then f.pathFlow i p else 0) ≤ f.node i v := by
  have h := node_marginal_le (f.pathFlow i) (f.transport i) 1
    (f.pathFlow_unit i) (f.pathFlow_arcs_le i) v
  have heq : (∑ p, f.pathFlow i p * nodeVisits p.val v) =
      ∑ p, if v ∈ p.val.support then f.pathFlow i p else 0 := by
    simp only [nodeVisits_path, mul_ite, mul_one, mul_zero]
  rw [heq] at h
  have hi := f.incoming_balance i v
  linarith

/-- A genuine feasible path LP obtained by positive-path bottleneck extraction.
Its existence is proved from compact conservation, not assumed as a witness. -/
def toNodeLP : UpperBound.NodeLP G h where
  source := f.source
  target := f.target
  buying := f.buying
  physical := f.physical
  demand := f.demand
  opening := f.opening
  flow := f.pathFlow
  buying_nonneg := f.buying_nonneg
  physical_nonneg := f.physical_nonneg
  demand_pos := f.demand_pos
  opening_bounds := f.opening_bounds
  flow_nonneg := f.pathFlow_nonneg
  unit := f.pathFlow_unit
  capacity := fun i v => (f.pathFlow_nodes_le i v).trans (f.capacity i v)
  source_buying := f.source_buying
  source_physical := f.source_physical
  target_buying := f.target_buying
  target_physical := f.target_physical

@[simp] theorem toNodeLP_buyingBudget : f.toNodeLP.buyingBudget = f.buyingBudget := rfl

theorem toNodeLP_fractionalLength_le (i : Fin h) :
    f.toNodeLP.fractionalLength i ≤ f.fractionalLength i := by
  rw [← f.toNodeLP.toCompact_fractionalLength i]
  apply Finset.sum_le_sum
  intro v _
  apply mul_le_mul_of_nonneg_left _ (f.physical_nonneg v)
  exact (f.toNodeLP.compactNode_eq i v).le.trans (f.pathFlow_nodes_le i v)

theorem toNodeLP_rentalBudget_le : f.toNodeLP.rentalBudget ≤ f.rentalBudget := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (f.toNodeLP_fractionalLength_le i) (le_of_lt (f.demand_pos i))

end Solution
end BuyAtBulk.CompactFlow
