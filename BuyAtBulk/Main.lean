import BuyAtBulk.Model.IntegralEmbedding
import BuyAtBulk.TheoremStatements
import BuyAtBulk.Statements.ZeroBuying
import BuyAtBulk.LowerBound.NodeGap
import BuyAtBulk.EdgeOnlyGap.Items.Theorem1
import BuyAtBulk.EdgeOnlyGap.Items.FiniteGap
import BuyAtBulk.EdgeOnlyGap.Items.ZeroLeavesOptima
import BuyAtBulk.UpperBound.ParameterizedRounding
import BuyAtBulk.UpperBound.Optimization
import BuyAtBulk.Statements.UniformApproximation
import BuyAtBulk.Statements.GraphRounding
import BuyAtBulk.Computation.OriginalPipeline
import BuyAtBulk.Computation.StoredOriginal
import BuyAtBulk.Computation.OriginalInitialization
import BuyAtBulk.Computation.PolynomialLP.Polynomial
import BuyAtBulk.Computation.Runtime.ParameterizedPolynomial
import BuyAtBulk.Computation.Runtime.OriginalIntegral
import BuyAtBulk.Computation.Runtime.OriginalPolynomial
import BuyAtBulk.Computation.Runtime.SuppliedPolynomial
import BuyAtBulk.Computation.Runtime.ComputedNetwork
import BuyAtBulk.Computation.Runtime.SparseSuppliedPolynomial
import BuyAtBulk.Computation.Rounding.SelectedZero

/-! Public paper results: separate-budget rounding, the node-cost gap, exact
computed LP optimization, supplied-path-LP rounding and a graph-only
approximation with polynomial rational/integer operation counts and
intermediate binary word lengths. -/
namespace BuyAtBulk

/-- The natural LP is a relaxation, preserving the two budgets separately. -/
theorem integral_relaxation (I : Instance) (routing : I.IntegralRouting) :
    I.Feasible (I.toFractional routing) ∧
    I.buyingCost (I.toFractional routing) = I.integralBuyingCost routing ∧
    I.rentalCost (I.toFractional routing) = I.integralRentalCost routing := by
  exact ⟨I.toFractional_feasible routing,
    I.toFractional_buyingCost routing, I.toFractional_rentalCost routing⟩

/-- A genuine exact approximation in the zero-buying case, conditional only
on a feasible LP solution whose value lower-bounds every integral routing.
Computing such an LP solution and execution/runtime are separate obligations. -/
theorem zero_buying_approximation (I : Instance) (f : I.FractionalSolution)
    (feasible : I.Feasible f) (zero_buying : I.buyingCost f = 0)
    (lp_lower_bound : ∀ comparison : I.IntegralRouting,
      (I.buyingCost f : ℝ) + I.rentalCost f ≤
        (I.integralBuyingCost comparison : ℝ) + I.integralRentalCost comparison) :
    Statements.ApproximationOutput I 1 := by
  obtain ⟨routing, buying_zero, rental_le⟩ := I.zero_buying_rounding f feasible zero_buying
  apply Statements.approximation_of_separate_budgets I f 1 (by norm_num) lp_lower_bound
  refine ⟨routing, ?_, ?_⟩
  · simp [buying_zero, zero_buying]
  · simpa only [one_mul] using (show (I.integralRentalCost routing : ℝ) ≤ I.rentalCost f by
      exact_mod_cast rental_le)

/-- Full node-cost integrality gap for every number of requests h ≥ 2. -/
theorem node_lower_bound : NodeGapTarget := LowerBound.node_gap

/-- Edge-only natural-LP integrality-gap lower bound (separate note, Theorem 1). -/
theorem edge_lower_bound : EdgeGapTarget := EdgeOnlyGap.theorem1

/-- Intermediate results of the edge-only note: the nonnegative-cost gap (§5) and the
zero-price pendant reduction (§6). -/
theorem edge_gap_stages : EdgeGapStagesTarget :=
  ⟨fun H q g π hg base hq sparse => EdgeOnlyGap.finiteGap H q g π hg base hq sparse,
    fun D edge => EdgeOnlyGap.zeroLeavesOptima D edge⟩

/-- Uniform mathematical part of the parameterized rounding theorem. -/
theorem parameterized_rounding (I : Instance) (graph : Nonempty I.GraphRealization)
    (f : I.FractionalSolution) (hf : I.Feasible f) (ratio r : ℕ)
    (hratio : 8 ≤ ratio) (hr : 1 ≤ r) :
    Statements.ParameterizedRoundedOutput I f ratio r 500000 :=
  UpperBound.parameterized_rounding I graph f hf ratio r hratio hr

/-- Mathematical optimized rounding, with one absolute constant for all
finite graph instances, positive demands and feasible rational LP inputs. -/
theorem optimized_rounding : UniformRoundingTarget := by
  apply UpperBound.uniform_optimized_of_parameterized
  exact ⟨500000, by norm_num, parameterized_rounding⟩

/-- Uniform numerical approximation existence; no polynomial-time LP solver
or runtime claim is asserted by this mathematical theorem. -/
theorem approximation : UniformApproximationTarget :=
  Statements.uniform_approximation_of_rounding optimized_rounding

/-- Explicit bought-network form of the source parameterized theorem:
physical rental uses attained shortest distances in the bought network. -/
theorem graph_parameterized_rounding (I : Instance) (realization : I.GraphRealization)
    (f : I.FractionalSolution) (hf : I.Feasible f) (ratio r : ℕ)
    (hratio : 8 ≤ ratio) (hr : 1 ≤ r) :
    Statements.GraphRoundedOutput I realization f
      (500000 * Statements.buyingFactor I.requestCount ratio r)
      (500000 * ((r : ℝ) * Statements.gridLevels I.requestCount ratio)) :=
  Statements.graph_output_of_routes I realization f _ _
    (parameterized_rounding I ⟨realization⟩ f hf ratio r hratio hr)

/-- Optimized source graph-output conclusion, with one uniform constant. -/
def UniformGraphRoundingTarget : Prop :=
  ∃ constant : ℝ, 0 < constant ∧
    ∀ (I : Instance) (realization : I.GraphRealization)
      (f : I.FractionalSolution), I.Feasible f →
      Statements.GraphRoundedOutput I realization f
        (constant * Statements.optimizedFactor I.requestCount)
        (constant * Statements.optimizedFactor I.requestCount)

theorem graph_optimized_rounding : UniformGraphRoundingTarget := by
  obtain ⟨constant, positive, rounding⟩ := optimized_rounding
  refine ⟨constant, positive, ?_⟩
  intro I realization f feasible
  exact Statements.graph_output_of_routes I realization f _ _
    (rounding I ⟨realization⟩ f feasible)

/-- The named program returns actual original graph paths and respects both
budgets of its sparse fractional input. Runtime bounds are separate. -/
def ExecutableGraphRoundingTarget : Prop :=
  ∀ (D : GraphData) [DecidableEq D.Vertex] [DecidableRel D.graph.Adj]
    (n : ℕ) (numbering : D.Vertex ≃ Fin n)
    (input : Computation.OriginalPipeline.OriginalFractional D)
    (ratio r : ℕ), 8 ≤ ratio → 1 ≤ r →
    ∃ output,
      Computation.OriginalPipeline.run D input numbering ratio r = some output ∧
      (Computation.OriginalPipeline.outputBuying D output : ℝ) ≤
        500000 * Statements.buyingFactor D.requestCount ratio r *
          Computation.OriginalPipeline.buyingBudget D input ∧
      (Computation.OriginalPipeline.outputRental D output : ℝ) ≤
        500000 * ((r : ℝ) * Statements.gridLevels D.requestCount ratio) *
          Computation.OriginalPipeline.rentalBudget D input ∧
      (output.routes.map fun entry => entry.1).Perm (List.finRange D.requestCount) ∧
      ∀ entry ∈ output.routes, ∀ a,
        Computation.OriginalPipeline.usesResource D entry.1 entry.2 a = true → a ∈ output.bought

theorem executable_graph_rounding : ExecutableGraphRoundingTarget := by
  intro D vertexEquality graphAdjacency n numbering input ratio r ratio_ge r_ge
  exact Computation.OriginalPipeline.run_correct D input numbering ratio r ratio_ge r_ge

/-- Finite stored arrays and indexed weighted paths feed the same named
program, without arbitrary graph or numerical callbacks. -/
def StoredGraphRoundingTarget : Prop :=
  ∀ (n resources requests : ℕ) (tables : Computation.StoredOriginal.Tables n resources requests)
    (input : Computation.StoredOriginal.Fractional tables)
    (ratio r : ℕ), 8 ≤ ratio → 1 ≤ r →
    ∃ output,
      Computation.StoredOriginal.run tables input ratio r = some output ∧
      (Computation.OriginalPipeline.outputBuying tables.graphData output : ℝ) ≤
        500000 * Statements.buyingFactor requests ratio r *
          Computation.OriginalPipeline.buyingBudget tables.graphData (input.decode tables) ∧
      (Computation.OriginalPipeline.outputRental tables.graphData output : ℝ) ≤
        500000 * ((r : ℝ) * Statements.gridLevels requests ratio) *
          Computation.OriginalPipeline.rentalBudget tables.graphData (input.decode tables) ∧
      (output.routes.map fun entry => entry.1).Perm (List.finRange requests) ∧
      ∀ entry ∈ output.routes, ∀ a,
        Computation.OriginalPipeline.usesResource tables.graphData entry.1 entry.2 a = true → a ∈ output.bought

theorem stored_graph_rounding : StoredGraphRoundingTarget := by
  intro n resources requests tables input ratio r ratio_ge r_ge
  exact Computation.StoredOriginal.run_correct tables input ratio r ratio_ge r_ge

/-- Graph-only initialization returns a computed feasible LP seed or an
actual disconnected request, ruling out fractional and integral solutions. -/
def GraphInitializationTarget : Prop :=
  ∀ (n resources requests : ℕ) (tables : Computation.StoredOriginal.Tables n resources requests),
    Computation.StoredOriginal.InitializationSpec tables
      (Computation.StoredOriginal.initializeChecked tables)

theorem graph_initialization : GraphInitializationTarget := by
  intro n resources requests tables
  exact Computation.StoredOriginal.initializeChecked_correct tables

/-- Unconditional exact stored rational LP optimization on the unit cube,
with globally fixed polynomial operation and intermediate-word bounds. -/
theorem exact_polynomial_lp : PolynomialLP.Polynomial.ExactPolynomialOptimizerTarget :=
  PolynomialLP.Polynomial.exactPolynomialOptimizer

/-- Arbitrary rounding parameters are charged by their binary lengths. -/
theorem parameterized_polynomial :
    Computation.Runtime.StoredRounding.ParameterizedPolynomialTarget :=
  Computation.Runtime.StoredRounding.parameterized_polynomial

/-- The computed original routing compares with every integral bought network. -/
theorem integral_graph_approximation :
    Computation.Runtime.Original.IntegralGraphApproximationTarget :=
  Computation.Runtime.Original.integral_graph_approximation

/-- Graph-only approximation, disconnected-input detection, and fixed
polynomial operation/word bounds in an explicit binary input encoding. -/
theorem polynomial_graph_approximation :
    Computation.Runtime.Original.PolynomialGraphApproximationTarget :=
  Computation.Runtime.Original.polynomial_graph_approximation

/-- Full supplied-original-path-LP rounding with arbitrary binary parameters,
actual original output guarantees, and polynomial operation/word bounds in
an explicit encoding of the graph, openings, weighted paths and parameters. -/
theorem supplied_polynomial_rounding :
    Computation.Runtime.Supplied.SuppliedPolynomialTarget :=
  Computation.Runtime.Supplied.supplied_polynomial

/-- Arbitrary selected zero-rental requests, with the original request count
in the logarithmic buying bound and exact selected output coverage. -/
theorem selected_zero_rounding : Computation.Rounding.SelectedZeroRoundingTarget :=
  Computation.Rounding.selected_zero_rounding_target

/-- Shortest-distance guarantees for precisely the purchase flags returned by
the supplied-input and graph-only programs. -/
theorem computed_network_rounding :
    Computation.Runtime.ComputedNetwork.ComputedNetworkTarget :=
  Computation.Runtime.ComputedNetwork.computed_networks

/-- Supplied weighted paths are aggregated and sparsified with unchanged buying,
nonincreasing rental, and polynomial runtime, word and output encoding bounds. -/
theorem supplied_sparse_decomposition :
    Computation.Runtime.SparseSupplied.SuppliedSparsePolynomialTarget :=
  Computation.Runtime.SparseSupplied.supplied_sparse_polynomial

/-- Combined proved mathematical results and computational contracts.
The computation model counts rational/integer word operations and bounds
intermediate words; the public contracts are documented in statements.md. -/
theorem paper_main : UniformRoundingTarget ∧ UniformApproximationTarget ∧ NodeGapTarget ∧
    EdgeGapTarget ∧ EdgeGapStagesTarget ∧
    UniformGraphRoundingTarget ∧ ExecutableGraphRoundingTarget ∧ StoredGraphRoundingTarget ∧
    GraphInitializationTarget ∧ PolynomialLP.Polynomial.ExactPolynomialOptimizerTarget ∧
    Computation.Runtime.StoredRounding.ParameterizedPolynomialTarget ∧
    Computation.Runtime.Original.IntegralGraphApproximationTarget ∧
    Computation.Runtime.Original.PolynomialGraphApproximationTarget ∧
    Computation.Runtime.Supplied.SuppliedPolynomialTarget ∧
    Computation.Rounding.SelectedZeroRoundingTarget ∧
    Computation.Runtime.ComputedNetwork.ComputedNetworkTarget ∧
    Computation.Runtime.SparseSupplied.SuppliedSparsePolynomialTarget :=
  ⟨optimized_rounding, approximation, node_lower_bound, edge_lower_bound, edge_gap_stages,
    graph_optimized_rounding,
    executable_graph_rounding, stored_graph_rounding, graph_initialization,
    exact_polynomial_lp, parameterized_polynomial, integral_graph_approximation,
    polynomial_graph_approximation, supplied_polynomial_rounding,
    selected_zero_rounding, computed_network_rounding, supplied_sparse_decomposition⟩

end BuyAtBulk
