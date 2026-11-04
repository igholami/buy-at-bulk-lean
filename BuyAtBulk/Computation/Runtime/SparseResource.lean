import BuyAtBulk.Computation.OriginalPipeline.Input

/-! Directed-flow domination preserves all original node and edge resources. -/
namespace BuyAtBulk.Computation.Runtime
open BuyAtBulk.CompactFlow
open BuyAtBulk.Computation
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem visits_edge_count {s t : V} (p : G.Walk s t) (u v : V) (hne : u ≠ v) :
    transportVisits p u v + transportVisits p v u = (p.edges.count s(u,v) : ℚ) := by
  induction p with
  | nil => simp [transportVisits]
  | @cons a b t hab p ih =>
    simp only [transportVisits, SimpleGraph.Walk.edges_cons, List.count_cons, Nat.cast_add]
    by_cases h₁ : a = u ∧ b = v <;> by_cases h₂ : a = v ∧ b = u <;>
      simp [Sym2.eq_iff, h₁, h₂] <;> grind

 theorem path_edge_visits {s t : V} (p : G.Path s t) (u v : V) (hne : u ≠ v) :
    (if s(u,v) ∈ p.val.edges then (1 : ℚ) else 0) =
      transportVisits p.val u v + transportVisits p.val v u := by
  rw [visits_edge_count p.val u v hne]
  by_cases hm : s(u,v) ∈ p.val.edges
  · rw [if_pos hm, List.nodup_iff_count_eq_one.mp p.property.isTrail.edges_nodup _ hm]
    norm_num
  · simp [hm, List.count_eq_zero.mpr hm]

 theorem list_node_marginal_identity {s t : V} (entries : FlowDecomposition.WeightedPaths G s t) (v : V) :
    (entries.map fun e => e.1 * nodeVisits e.2.val v).sum =
      (∑ u, (entries.map fun e => e.1 * transportVisits e.2.val u v).sum) +
      (entries.map Prod.fst).sum * (if s = v then 1 else 0) := by
  induction entries with
  | nil => simp
  | cons e rest ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
    rw [ih, visits_incoming]
    simp only [mul_add, Finset.mul_sum]
    ring

 theorem list_node_marginal_le {s t : V} (input output : FlowDecomposition.WeightedPaths G s t)
    (unit : (output.map Prod.fst).sum = (input.map Prod.fst).sum)
    (dom : ∀ u v, (output.map fun e => e.1 * transportVisits e.2.val u v).sum ≤
      (input.map fun e => e.1 * transportVisits e.2.val u v).sum) (v : V) :
    (output.map fun e => e.1 * nodeVisits e.2.val v).sum ≤
      (input.map fun e => e.1 * nodeVisits e.2.val v).sum := by
  rw [list_node_marginal_identity, list_node_marginal_identity, unit]
  exact add_le_add (Finset.sum_le_sum fun u _ => dom u v) le_rfl

theorem list_edge_marginal_le {s t : V} (input output : FlowDecomposition.WeightedPaths G s t)
    (dom : ∀ u v, (output.map fun e => e.1 * transportVisits e.2.val u v).sum ≤
      (input.map fun e => e.1 * transportVisits e.2.val u v).sum)
    (u v : V) (hne : u ≠ v) :
    (output.map fun e => if s(u,v) ∈ e.2.val.edges then e.1 else 0).sum ≤
      (input.map fun e => if s(u,v) ∈ e.2.val.edges then e.1 else 0).sum := by
  have identity (entries : FlowDecomposition.WeightedPaths G s t) :
      (entries.map fun e => if s(u,v) ∈ e.2.val.edges then e.1 else 0).sum =
      (entries.map fun e => e.1 * transportVisits e.2.val u v).sum +
      (entries.map fun e => e.1 * transportVisits e.2.val v u).sum := by
    calc
      _ = (entries.map fun e => e.1 * (if s(u,v) ∈ e.2.val.edges then 1 else 0)).sum := by
        simp only [mul_ite, mul_one, mul_zero]
      _ = _ := by
        simp only [path_edge_visits _ u v hne, mul_add, List.sum_map_add]
  rw [identity, identity]
  exact add_le_add (dom u v) (dom v u)

 theorem original_resource_marginal_le (D : GraphData) [DecidableEq D.Vertex]
    [DecidableRel D.graph.Adj] (i : Fin D.requestCount)
    (input output : FlowDecomposition.WeightedPaths D.graph (D.source i) (D.target i))
    (unit : (output.map Prod.fst).sum = (input.map Prod.fst).sum)
    (dom : ∀ u v, (output.map fun e => e.1 * transportVisits e.2.val u v).sum ≤
      (input.map fun e => e.1 * transportVisits e.2.val u v).sum)
    (a : Fin D.resourceCount) :
    (output.map fun e => if OriginalPipeline.usesResource D i e.2 a then e.1 else 0).sum ≤
      (input.map fun e => if OriginalPipeline.usesResource D i e.2 a then e.1 else 0).sum := by
  cases loc : D.location a with
  | inl v =>
    simpa only [OriginalPipeline.usesResource, loc, decide_eq_true_eq, nodeVisits_path,
      mul_ite, mul_one, mul_zero] using list_node_marginal_le input output unit dom v
  | inr edge =>
    induction edge using Sym2.ind with
    | _ u v =>
      have adj : D.graph.Adj u v := by
        have valid := D.location_valid a
        simpa [loc] using valid
      simpa only [OriginalPipeline.usesResource, loc, decide_eq_true_eq] using
        list_edge_marginal_le input output dom u v adj.ne

namespace OriginalSparse
variable (D : GraphData) [DecidableEq D.Vertex] [DecidableRel D.graph.Adj]
    (input : OriginalPipeline.OriginalFractional D)
    (paths : ∀ i, FlowDecomposition.WeightedPaths D.graph (D.source i) (D.target i))
    (nonneg : ∀ i e, e ∈ paths i → 0 ≤ e.1)
    (unit : ∀ i, ((paths i).map Prod.fst).sum = 1)
    (dom : ∀ i u v, ((paths i).map fun e => e.1 * transportVisits e.2.val u v).sum ≤
      ((input.paths i).map fun e => e.1 * transportVisits e.2.val u v).sum)

 def ofDominated : OriginalPipeline.OriginalFractional D where
  opening := input.opening
  paths := paths
  opening_bounds := input.opening_bounds
  nonneg := nonneg
  unit := unit
  capacity := by
    intro i a
    exact (original_resource_marginal_le D i (input.paths i) (paths i)
      ((unit i).trans (input.unit i).symm) (dom i) a).trans (input.capacity i a)

 theorem buying_eq : OriginalPipeline.buyingBudget D (ofDominated D input paths nonneg unit dom) =
      OriginalPipeline.buyingBudget D input := rfl

 private theorem resource_cost_sum (i : Fin D.requestCount)
    (entries : FlowDecomposition.WeightedPaths D.graph (D.source i) (D.target i)) :
    (entries.map fun e => e.1 * OriginalPipeline.pathResourceCost D D.length i e.2).sum =
      ∑ a, D.length a * (entries.map fun e => if OriginalPipeline.usesResource D i e.2 a then e.1 else 0).sum := by
    induction entries with
    | nil => simp
    | cons e rest ih =>
      simp only [List.map_cons, List.sum_cons, ih, mul_add, Finset.sum_add_distrib]
      congr 1
      unfold OriginalPipeline.pathResourceCost
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      split <;> simp_all [mul_comm]

 theorem length_le (i : Fin D.requestCount) :
    OriginalPipeline.fractionalLength D (ofDominated D input paths nonneg unit dom) i ≤
      OriginalPipeline.fractionalLength D input i := by
    change ((paths i).map _).sum ≤ ((input.paths i).map _).sum
    rw [resource_cost_sum, resource_cost_sum]
    apply Finset.sum_le_sum
    intro a _
    exact mul_le_mul_of_nonneg_left (original_resource_marginal_le D i (input.paths i) (paths i)
      ((unit i).trans (input.unit i).symm) (dom i) a) (D.length_nonneg a)

 theorem rental_le : OriginalPipeline.rentalBudget D (ofDominated D input paths nonneg unit dom) ≤
      OriginalPipeline.rentalBudget D input := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (length_le D input paths nonneg unit dom i) (D.demand_pos i).le
end OriginalSparse
end BuyAtBulk.Computation.Runtime
