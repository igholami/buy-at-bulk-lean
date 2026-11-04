import BuyAtBulk.Computation.OriginalPipeline.Input
import BuyAtBulk.Model.NodeReduction.EndpointEmbedding

/-! Actual subdivision and sparse compact-flow coordinates, preserving both original budgets. -/
set_option maxHeartbeats 1800000
namespace BuyAtBulk.Computation.OriginalPipeline
open BuyAtBulk.NodeReduction BuyAtBulk.CompactFlow
open scoped BuyAtBulk.Computation.NodeReduction
variable (D : GraphData) [DecidableEq D.Vertex] (input : OriginalFractional D)

def liftedEntries (i : Fin D.requestCount) :
    FlowDecomposition.WeightedPaths (graph D) (Vertex.leaf i false) (Vertex.leaf i true) :=
  (input.paths i).map fun entry => (entry.1, liftPath D i entry.2)

theorem lifted_nonneg (i : Fin D.requestCount) :
    ∀ entry ∈ liftedEntries D input i, 0 ≤ entry.1 := by
  intro entry member
  obtain ⟨entry, entry_mem, rfl⟩ := List.mem_map.mp member
  exact input.nonneg i entry entry_mem

theorem lifted_unit (i : Fin D.requestCount) :
    ((liftedEntries D input i).map Prod.fst).sum = 1 := by
  simpa [liftedEntries, List.map_map, Function.comp_def] using input.unit i

theorem list_nodes {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {s t : V} (entries : FlowDecomposition.WeightedPaths G s t) (v : V) :
    (∑ p, if v ∈ p.val.support then FlowDecomposition.listFlow G entries p else 0) =
      (entries.map fun entry => if v ∈ entry.2.val.support then entry.1 else 0).sum := by
  classical
  have weighted := FlowDecomposition.weighted_listFlow G entries
    (fun p => if v ∈ p.val.support then (1 : ℚ) else 0)
  simpa only [mul_ite, mul_one, mul_zero] using weighted

theorem list_node_le_mass {V : Type} [DecidableEq V] {G : SimpleGraph V}
    {s t : V} (entries : FlowDecomposition.WeightedPaths G s t) (v : V)
    (nonneg : ∀ entry ∈ entries, 0 ≤ entry.1) :
    (entries.map fun entry => if v ∈ entry.2.val.support then entry.1 else 0).sum ≤
      (entries.map Prod.fst).sum := by
  induction entries with
  | nil => simp
  | cons entry rest ih =>
    have head := nonneg entry (by simp)
    have tail := ih (fun e member => nonneg e (by simp [member]))
    simp only [List.map_cons, List.sum_cons]
    split_ifs <;> linarith

theorem lifted_capacity (i : Fin D.requestCount) (v : Vertex D) :
    ((liftedEntries D input i).map fun entry => if v ∈ entry.2.val.support then entry.1 else 0).sum ≤
      resourceOpening D input.opening v := by
  by_cases paid : ∃ a, resourceVertex D a = v
  · obtain ⟨a, rfl⟩ := paid
    rw [resourceOpening_resource]
    have bound := input.capacity i a
    convert bound using 1
    unfold liftedEntries
    rw [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro entry _
    have exact_mem := liftPath_resource_mem D i entry.2 a
    cases location : D.location a <;> simp_all [usesResource]
  · rw [resourceOpening_free D input.opening v (by simpa using paid)]
    exact (list_node_le_mass (liftedEntries D input i) v (lifted_nonneg D input i)).trans_eq (lifted_unit D input i)

variable [DecidableRel D.graph.Adj]

/-- All LP data are executable; path flow lookup scans only the input sparse
list after actual structural subdivision. -/
def nodeLP : UpperBound.NodeLP (graph D) D.requestCount where
  source := fun i => Vertex.leaf i false
  target := fun i => Vertex.leaf i true
  buying := resourceCost D D.buying
  physical := resourceCost D D.length
  demand := D.demand
  opening := resourceOpening D input.opening
  flow := fun i => FlowDecomposition.listFlow (graph D) (liftedEntries D input i)
  buying_nonneg := by intro v; rw [resourceCost_eq]; exact nodeCost_nonneg D D.buying D.buying_nonneg v
  physical_nonneg := by intro v; rw [resourceCost_eq]; exact nodeCost_nonneg D D.length D.length_nonneg v
  demand_pos := D.demand_pos
  opening_bounds := resourceOpening_bounds D input.opening input.opening_bounds
  flow_nonneg := by
    intro i p
    apply List.sum_nonneg
    intro q member
    obtain ⟨entry, entry_mem, rfl⟩ := List.mem_map.mp member
    split_ifs
    · exact lifted_nonneg D input i entry entry_mem
    · exact le_rfl
  unit := by
    intro i
    have weighted := FlowDecomposition.weighted_listFlow (graph D) (liftedEntries D input i) (fun _ => 1)
    simp only [mul_one] at weighted
    convert weighted.trans (lifted_unit D input i) using 1
    apply Finset.sum_congr (univ_independent _ _)
    intro p _; rfl
  capacity := by
    intro i v
    convert (list_nodes (liftedEntries D input i) v).le.trans (lifted_capacity D input i v) using 1
    apply Finset.sum_congr (univ_independent _ _)
    intro p _
    split_ifs <;> rfl
  source_buying := by intro i; rw [resourceCost_eq, nodeCost_leaf]
  source_physical := by intro i; rw [resourceCost_eq, nodeCost_leaf]
  target_buying := by intro i; rw [resourceCost_eq, nodeCost_leaf]
  target_physical := by intro i; rw [resourceCost_eq, nodeCost_leaf]

theorem nodeLP_buying : (nodeLP D input).buyingBudget = buyingBudget D input := by
  classical
  calc
    (nodeLP D input).buyingBudget =
        ∑ v, nodeCost D D.buying v * resourceOpening D input.opening v := by
      apply Finset.sum_congr (univ_independent _ _)
      intro v _
      exact congrArg (fun q => q * resourceOpening D input.opening v) (resourceCost_eq D D.buying v)
    _ = ∑ a, D.buying a * resourceOpening D input.opening (resourceVertex D a) :=
      nodeCost_budget D D.buying (resourceOpening D input.opening)
    _ = buyingBudget D input := by simp [buyingBudget]

theorem lifted_resourceCost (cost : Fin D.resourceCount → ℚ) (i : Fin D.requestCount)
    (path : D.graph.Path (D.source i) (D.target i)) :
    NodeMetric.walkWeight (graph D) (resourceCost D cost) (liftPath D i path).val =
      pathResourceCost D cost i path := by
  classical
  rw [show resourceCost D cost = nodeCost D cost from funext (resourceCost_eq D cost)]
  rw [nodeCost_walk]
  unfold pathResourceCost
  apply Finset.sum_congr rfl
  intro a _
  have exact_mem := liftPath_resource_mem D i path a
  cases location : D.location a <;> simp_all [usesResource]

theorem nodeLP_length (i : Fin D.requestCount) :
    (nodeLP D input).fractionalLength i = fractionalLength D input i := by
  classical
  calc
    (nodeLP D input).fractionalLength i =
        ∑ p, FlowDecomposition.listFlow (graph D) (liftedEntries D input i) p *
          NodeMetric.walkWeight (graph D) (resourceCost D D.length) p.val := by
      apply Finset.sum_congr (univ_independent _ _)
      intro p _
      exact mul_comm _ _
    _ = ((liftedEntries D input i).map fun entry =>
        entry.1 * NodeMetric.walkWeight (graph D) (resourceCost D D.length) entry.2.val).sum :=
      FlowDecomposition.weighted_listFlow (graph D) (liftedEntries D input i) _
    _ = fractionalLength D input i := by
      simp [liftedEntries, fractionalLength, List.map_map, Function.comp_def, lifted_resourceCost]

/-- Computed compact node/arc coordinates, built from the actual lifted input
lists. No enumeration of the full path space is evaluated. -/
def compact : CompactFlow.Solution (graph D) D.requestCount :=
  forward (nodeLP D input) (liftedEntries D input) (fun _ _ => rfl)

@[simp] theorem compact_buying : (compact D input).buyingBudget = buyingBudget D input := by
  exact (forward_buying _ _ _).trans (nodeLP_buying D input)

theorem compact_length (i : Fin D.requestCount) :
    (compact D input).fractionalLength i = fractionalLength D input i := by
  exact (forward_length _ _ _ i).trans (nodeLP_length D input i)

@[simp] theorem compact_rental : (compact D input).rentalBudget = rentalBudget D input := by
  unfold CompactFlow.Solution.rentalBudget rentalBudget
  simp only [compact_length]
  rfl

end BuyAtBulk.Computation.OriginalPipeline
