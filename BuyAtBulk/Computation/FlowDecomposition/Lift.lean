import BuyAtBulk.Computation.FlowDecomposition
import BuyAtBulk.Model.CompactFlowReverse
import BuyAtBulk.Computation.ShortestPath.Traversal

/-! Computed sparse path lists for every commodity of a compact solution.
The supplied numbering controls storage and iteration; the output paths are
paths of the original graph. -/
set_option maxHeartbeats 1600000
namespace BuyAtBulk.Computation.FlowDecomposition
open BuyAtBulk.CompactFlow
private theorem univ_independent {P : Type} (a b : Fintype P) :
    @Finset.univ P a = @Finset.univ P b := by
  rw [Subsingleton.elim a b]

variable {V : Type} [Fintype V] [DecidableEq V] {n h : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (numbering : V ≃ Fin n)

def storedMatrix (f : CompactFlow.Solution G h) (i : Fin h) : FlowMatrix n :=
  Vector.ofFn fun u => Vector.ofFn fun v => f.transport i (numbering.symm u) (numbering.symm v)

@[simp] theorem decoded_storedMatrix (f : CompactFlow.Solution G h) (i : Fin h) (u v : V) :
    decodedFlow numbering (storedMatrix G numbering f i) u v = f.transport i u v := by
  simp [storedMatrix, decodedFlow, matrixFlow, Vector.getElem_ofFn]

theorem stored_verified (f : CompactFlow.Solution G h) (i : Fin h) :
    ∃ entries, VerifiedDecomposition G numbering (storedMatrix G numbering f i)
      (f.source i) (f.target i) entries := by
  apply decompose_verified G numbering
  · simpa using f.transport_nonneg i
  · simpa using f.transport_le_one i
  · simpa using f.transport_nonedge i
  · intro v
    simp only [decoded_storedMatrix]
    have hin := f.incoming_balance i v
    have hout := f.outgoing_balance i v
    split_ifs at hin hout ⊢ <;> simp_all <;> linarith

def entries (f : CompactFlow.Solution G h) (i : Fin h) :
    WeightedPaths G (f.source i) (f.target i) :=
  (decompose G numbering (storedMatrix G numbering f i) (f.source i) (f.target i)).get
    (by obtain ⟨entries, correct⟩ := stored_verified G numbering f i
        rw [correct.returned]; trivial)

theorem entries_verified (f : CompactFlow.Solution G h) (i : Fin h) :
    VerifiedDecomposition G numbering (storedMatrix G numbering f i)
      (f.source i) (f.target i) (entries G numbering f i) := by
  obtain ⟨result, correct⟩ := stored_verified G numbering f i
  have equal : entries G numbering f i = result := by simp [entries, correct.returned]
  exact equal.symm ▸ correct

/-- Finite list evaluation; equality is structural equality of actual paths. -/
def listFlow {s t : V} (entries : WeightedPaths G s t) (p : G.Path s t) : ℚ :=
  (entries.map fun entry => if entry.2 = p then entry.1 else 0).sum

theorem weighted_listFlow {s t : V} (entries : WeightedPaths G s t)
    (weight : G.Path s t → ℚ) :
    (∑ p, listFlow G entries p * weight p) =
      (entries.map fun entry => entry.1 * weight entry.2).sum := by
  classical
  induction entries with
  | nil => simp [listFlow]
  | cons entry rest ih =>
    simp only [listFlow, List.map_cons, List.sum_cons] at *
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib, ih]
    congr 1
    simp

theorem listFlow_nonneg {s t : V} (entries : WeightedPaths G s t)
    (positive : ∀ entry ∈ entries, 0 < entry.1) (p : G.Path s t) :
    0 ≤ listFlow G entries p := by
  apply List.sum_nonneg
  intro q member
  obtain ⟨entry, entry_mem, rfl⟩ := List.mem_map.mp member
  split_ifs
  · exact (positive entry entry_mem).le
  · exact le_rfl

theorem entries_unit (f : CompactFlow.Solution G h) (i : Fin h) :
    ∑ p, listFlow G (entries G numbering f i) p = 1 := by
  simpa using (weighted_listFlow G (entries G numbering f i) (fun _ => 1)).trans
    (by simpa using (entries_verified G numbering f i).unit)

theorem entries_arcs (f : CompactFlow.Solution G h) (i : Fin h) (u v : V) :
    (∑ p, listFlow G (entries G numbering f i) p * transportVisits p.val u v) ≤ f.transport i u v := by
  rw [weighted_listFlow]
  simpa using (entries_verified G numbering f i).arc_dominated u v

theorem entries_nodes (f : CompactFlow.Solution G h) (i : Fin h) (v : V) :
    (∑ p, if v ∈ p.val.support then listFlow G (entries G numbering f i) p else 0) ≤ f.node i v := by
  classical
  have bound := node_marginal_le (listFlow G (entries G numbering f i)) (f.transport i) 1
    (by convert entries_unit G numbering f i using 1 <;> apply Finset.sum_congr (univ_independent _ _) <;> intros <;> first | rfl | (split_ifs <;> rfl))
    (by intro u v; convert entries_arcs G numbering f i u v using 1 <;> apply Finset.sum_congr (univ_independent _ _) <;> intros <;> first | rfl | (split_ifs <;> rfl)) v
  simp only [nodeVisits_path, mul_ite, mul_one, mul_zero] at bound
  have incoming := f.incoming_balance i v
  have bound' : (∑ p, if v ∈ p.val.support then listFlow G (entries G numbering f i) p else 0) ≤
      (∑ u, f.transport i u v) + (if f.source i = v then 1 else 0) := by
    convert bound using 1 <;> first | (apply Finset.sum_congr (univ_independent _ _) <;> intros <;> first | rfl | (split_ifs <;> rfl)) | simp
  split_ifs at incoming bound' <;> linarith

/-- A feasible path LP whose flow is evaluated from the computed sparse lists. -/
def toNodeLP (f : CompactFlow.Solution G h) : UpperBound.NodeLP G h where
  source := f.source
  target := f.target
  buying := f.buying
  physical := f.physical
  demand := f.demand
  opening := f.opening
  flow := fun i => listFlow G (entries G numbering f i)
  buying_nonneg := f.buying_nonneg
  physical_nonneg := f.physical_nonneg
  demand_pos := f.demand_pos
  opening_bounds := f.opening_bounds
  flow_nonneg := fun i => listFlow_nonneg G _ (entries_verified G numbering f i).weights_positive
  unit := by intro i; convert entries_unit G numbering f i using 1 <;> apply Finset.sum_congr (univ_independent _ _) <;> intros <;> first | rfl | (split_ifs <;> rfl)
  capacity := by
    intro i v
    convert (entries_nodes G numbering f i v).trans (f.capacity i v) using 1 <;> apply Finset.sum_congr (univ_independent _ _) <;> intros <;> first | rfl | (split_ifs <;> rfl)
  source_buying := f.source_buying
  source_physical := f.source_physical
  target_buying := f.target_buying
  target_physical := f.target_physical

@[simp] theorem toNodeLP_buyingBudget (f : CompactFlow.Solution G h) :
    (toNodeLP G numbering f).buyingBudget = f.buyingBudget := rfl

theorem toNodeLP_fractionalLength_le (f : CompactFlow.Solution G h) (i : Fin h) :
    (toNodeLP G numbering f).fractionalLength i ≤ f.fractionalLength i := by
  rw [← (toNodeLP G numbering f).toCompact_fractionalLength i]
  apply Finset.sum_le_sum
  intro v _
  apply mul_le_mul_of_nonneg_left _ (f.physical_nonneg v)
  apply ((toNodeLP G numbering f).compactNode_eq i v).le.trans
  convert entries_nodes G numbering f i v using 1 <;> apply Finset.sum_congr (univ_independent _ _) <;> intros <;> simp only [toNodeLP] <;> split_ifs <;> simp_all

theorem toNodeLP_rentalBudget_le (f : CompactFlow.Solution G h) :
    (toNodeLP G numbering f).rentalBudget ≤ f.rentalBudget := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (toNodeLP_fractionalLength_le G numbering f i) (f.demand_pos i).le

/-- Executable raw length metadata computed from the same returned entries. -/
def fractionalLength (f : CompactFlow.Solution G h) (i : Fin h) : ℚ :=
  ((entries G numbering f i).map fun entry =>
    entry.1 * ShortestPath.traversalCost G f.physical entry.2.val).sum

theorem fractionalLength_eq (f : CompactFlow.Solution G h) (i : Fin h) :
    fractionalLength G numbering f i = (toNodeLP G numbering f).fractionalLength i := by
  classical
  have semantic : (toNodeLP G numbering f).fractionalLength i =
      (∑ p, listFlow G (entries G numbering f i) p * NodeMetric.walkWeight G f.physical p.val) := by
    unfold UpperBound.NodeLP.fractionalLength
    apply Finset.sum_congr (univ_independent _ _)
    intro p _
    exact mul_comm _ _
  change fractionalLength G numbering f i = _
  rw [semantic]
  rw [weighted_listFlow]
  unfold fractionalLength
  apply congrArg List.sum
  apply List.map_congr_left
  intro entry _
  rw [ShortestPath.traversalCost_eq_supportWeight G f.physical entry.2.val entry.2.property]

end BuyAtBulk.Computation.FlowDecomposition
