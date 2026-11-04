import BuyAtBulk.Model.BoughtNetwork
import BuyAtBulk.Computation.Runtime.SuppliedRounding
import BuyAtBulk.Computation.Runtime.OriginalIntegral

/-! The network defined by the actual returned purchase flags, with the
paper's shortest physical distances. No existential replacement purchase set
is substituted for the computed output. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace BuyAtBulk.Computation.Runtime.ComputedNetwork
open BuyAtBulk.Computation.StoredOriginal Original
variable {n resources h : ℕ} (tables : Tables n resources h)

abbrev Network := tables.graphData.toInstance.BoughtNetwork tables.graphData.realization

def Covered (output : StoredOriginalOutput tables) : Prop :=
  (output.routes.map fun e => e.1).Perm (List.finRange h)

def Supported (output : StoredOriginalOutput tables) : Prop :=
  ∀ e ∈ output.routes, ∀ a, OriginalPipeline.usesResource tables.graphData e.1 e.2 a = true →
    output.bought[a.val] = true

theorem resource_iff (i : Fin h) (path : tables.graphData.graph.Path (tables.graphData.source i) (tables.graphData.target i))
    (a : Fin resources) :
    a ∈ tables.graphData.toInstance.walkResources tables.graphData.realization.location path.val ↔
      OriginalPipeline.usesResource tables.graphData i path a = true := by
  classical
  simp only [Instance.walkResources, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [GraphData.realization, OriginalPipeline.usesResource]
  split <;> simp_all

/-- Exact interpretation of the returned Boolean purchase vector. -/
def ofOutput (output : StoredOriginalOutput tables) (covered : Covered tables output)
    (supported : Supported tables output) : Network tables where
  resources := Finset.univ.filter fun a => output.bought[a.val] = true
  connected i := by
    have member : i ∈ output.routes.map (fun e => e.1) := covered.mem_iff.mpr (List.mem_finRange i)
    obtain ⟨⟨j,path⟩,present,same⟩ := List.mem_map.mp member
    dsimp at same
    subst j
    refine ⟨path, ?_⟩
    intro a used
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, supported _ present a ((resource_iff tables i path a).mp used)⟩

@[simp] theorem ofOutput_resources (output : StoredOriginalOutput tables) (covered : Covered tables output)
    (supported : Supported tables output) (a : Fin resources) :
    a ∈ (ofOutput tables output covered supported).resources ↔ output.bought[a.val] = true := by
  simp [ofOutput]

@[simp] theorem ofOutput_buying (output : StoredOriginalOutput tables) (covered : Covered tables output)
    (supported : Supported tables output) :
    (ofOutput tables output covered supported).buyingCost = outputBuying tables output := by
  classical
  simp only [Instance.BoughtNetwork.buyingCost, ofOutput, Finset.sum_filter, outputBuying]

theorem physicalLength_eq (network : Network tables) (i : Fin h)
    (path : tables.graphData.graph.Path (tables.graphData.source i) (tables.graphData.target i)) :
    network.physicalLength path.val = OriginalPipeline.pathResourceCost tables.graphData tables.graphData.length i path := by
  classical
  unfold Instance.BoughtNetwork.physicalLength OriginalPipeline.pathResourceCost
  rw [← Finset.sum_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact resource_iff tables i path a

theorem ofOutput_distance (output : StoredOriginalOutput tables) (covered : Covered tables output)
    (supported : Supported tables output) (entry : tables.graphData.TaggedPath) (member : entry ∈ output.routes) :
    (ofOutput tables output covered supported).distance entry.1 ≤
      OriginalPipeline.pathResourceCost tables.graphData tables.graphData.length entry.1 entry.2 := by
  have available : tables.graphData.toInstance.walkResources tables.graphData.realization.location entry.2.val ⊆
      (ofOutput tables output covered supported).resources := by
    intro a used
    exact (ofOutput_resources tables output covered supported a).mpr
      (supported entry member a ((resource_iff tables entry.1 entry.2 a).mp used))
  have bound := (ofOutput tables output covered supported).distance_le_path entry.1 entry.2 available
  simpa only [physicalLength_eq] using bound

theorem ofOutput_rental (output : StoredOriginalOutput tables) (covered : Covered tables output)
    (supported : Supported tables output) :
    (ofOutput tables output covered supported).rentalCost ≤ outputRental tables output := by
  let network := ofOutput tables output covered supported
  have sumEq : (output.routes.map fun entry => tables.demand[entry.1.val]*network.distance entry.1).sum =
      ∑ i : Fin h, tables.demand[i.val]*network.distance i := by
    have permuted := (covered.map fun i => tables.demand[i.val]*network.distance i).sum_eq
    simpa only [List.map_map,Function.comp_def,← Fin.sum_univ_def] using permuted
  change (∑ i : Fin h, tables.demand[i.val]*network.distance i) ≤ _
  rw [← sumEq]
  apply List.sum_le_sum
  intro entry member
  exact mul_le_mul_of_nonneg_left (ofOutput_distance tables output covered supported entry member)
    (tables.demand_pos entry.1).le

/-- This graph uses precisely the flags returned by the graph-only algorithm. -/
theorem closedRun_network (output : StoredOriginalOutput tables) (returned : closedRun tables = .ok output) :
    ∃ network : Network tables,
      (∀ a : Fin resources, a ∈ network.resources ↔ output.bought[a.val] = true) ∧
      network.buyingCost = outputBuying tables output ∧
      network.rentalCost ≤ outputRental tables output ∧
      ∀ comparison : IntegralInput tables,
        ((network.buyingCost + network.rentalCost : ℚ) : ℝ) ≤
          2500000000 * Statements.optimizedFactor h * (comparison.buying + comparison.rental) := by
  have correct := closedRun_correct tables
  rw [returned] at correct
  change SourceSpec tables (.ok (some output)) at correct
  let network := ofOutput tables output correct.1 correct.2.1
  refine ⟨network, ofOutput_resources tables output correct.1 correct.2.1,
    ofOutput_buying tables output correct.1 correct.2.1,
    ofOutput_rental tables output correct.1 correct.2.1, ?_⟩
  intro comparison
  have routeBound := closedRun_integral tables output returned comparison
  have buying := ofOutput_buying tables output correct.1 correct.2.1
  have rental := ofOutput_rental tables output correct.1 correct.2.1
  have sumBound : network.buyingCost + network.rentalCost ≤ outputBuying tables output + outputRental tables output := by
    dsimp only [network]
    rw [buying]
    exact add_le_add le_rfl rental
  exact (show ((network.buyingCost + network.rentalCost : ℚ) : ℝ) ≤
    ((outputBuying tables output + outputRental tables output : ℚ) : ℝ) by exact_mod_cast sumBound).trans routeBound

/-- Separate paper budgets, using shortest distances in the computed network. -/
theorem suppliedRun_network (fractional : Fractional tables) (ratio r : ℕ)
    (ratio_ge : 8 ≤ ratio) (r_ge : 1 ≤ r) :
    ∃ output : StoredOriginalOutput tables, ∃ network : Network tables,
      (Supplied.run tables fractional ratio r (by omega)).value = some output ∧
      (∀ a : Fin resources, a ∈ network.resources ↔ output.bought[a.val] = true) ∧
      network.buyingCost = outputBuying tables output ∧
      network.rentalCost ≤ outputRental tables output ∧
      (network.buyingCost : ℝ) ≤ 500000 * Statements.buyingFactor h ratio r *
        OriginalPipeline.buyingBudget tables.graphData fractional.decode ∧
      (network.rentalCost : ℝ) ≤ 500000 * ((r : ℝ) * Statements.gridLevels h ratio) *
        OriginalPipeline.rentalBudget tables.graphData fractional.decode := by
  obtain ⟨output,returned,buying,rental,covered,supported⟩ := Supplied.run_correct tables fractional ratio r ratio_ge r_ge
  let network := ofOutput tables output covered supported
  have same := ofOutput_buying tables output covered supported
  have shorter := ofOutput_rental tables output covered supported
  refine ⟨output,network,returned,ofOutput_resources tables output covered supported,same,shorter,?_,?_⟩
  · dsimp only [network]
    rw [same]
    exact buying
  · exact (show (network.rentalCost : ℝ) ≤ outputRental tables output by exact_mod_cast shorter).trans rental

/-- Public paper-network interface for both computed entry points. -/
def ComputedNetworkTarget : Prop :=
  ∀ (n resources h : ℕ) (tables : Tables n resources h),
    (∀ (output : StoredOriginalOutput tables), closedRun tables = .ok output →
      ∃ network : Network tables,
        (∀ a : Fin resources, a ∈ network.resources ↔ output.bought[a.val] = true) ∧
        network.buyingCost = outputBuying tables output ∧
        network.rentalCost ≤ outputRental tables output ∧
        ∀ comparison : IntegralInput tables,
          ((network.buyingCost + network.rentalCost : ℚ) : ℝ) ≤
            2500000000 * Statements.optimizedFactor h * (comparison.buying + comparison.rental)) ∧
    (∀ (fractional : Fractional tables) (ratio r : ℕ) (ratio_ge : 8 ≤ ratio) (r_ge : 1 ≤ r),
      ∃ output : StoredOriginalOutput tables, ∃ network : Network tables,
        (Supplied.run tables fractional ratio r (by omega)).value = some output ∧
        (∀ a : Fin resources, a ∈ network.resources ↔ output.bought[a.val] = true) ∧
        network.buyingCost = outputBuying tables output ∧
        network.rentalCost ≤ outputRental tables output ∧
        (network.buyingCost : ℝ) ≤ 500000 * Statements.buyingFactor h ratio r *
          OriginalPipeline.buyingBudget tables.graphData fractional.decode ∧
        (network.rentalCost : ℝ) ≤ 500000 * ((r : ℝ) * Statements.gridLevels h ratio) *
          OriginalPipeline.rentalBudget tables.graphData fractional.decode)

theorem computed_networks : ComputedNetworkTarget := by
  intro n resources h tables
  exact ⟨closedRun_network tables, suppliedRun_network tables⟩

end BuyAtBulk.Computation.Runtime.ComputedNetwork
