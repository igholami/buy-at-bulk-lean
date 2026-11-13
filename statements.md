# Main approximation theorem

This page contains the paper's main approximation theorem and the Lean
contracts needed to state its approximation, LP-gap and polynomial-runtime
guarantees, followed by the edge-only LP integrality-gap lower bound of the
extension note. Supporting lemmas, algorithms and unrelated results are omitted.
The Lean snippets are verbatim source excerpts in their original module context;
proof bodies are omitted. Source links provide the surrounding types and imports.

Paper: Theorem 1 (Unrestricted nonuniform buy-at-bulk), labeled
`thm:rounding` in the paper’s `introduction.tex`. The paper sources are not
bundled with this repository.

<!-- paper-source: introduction.tex -->
```latex
\begin{theorem}[Unrestricted nonuniform buy-at-bulk]\label{thm:rounding}
There is a deterministic polynomial-time
\begin{align*}
 &O\!\left(\frac{\log^2 h}{(\log\log h)^2}\right)
\end{align*}
approximation algorithm for undirected nonuniform buy-at-bulk network design with $h\ge3$ arbitrary terminal pairs and positive rational demands. For one or two requests, the algorithm has a constant approximation ratio. The guarantee holds for buying prices and physical lengths on edges, on nodes, or on both, and establishes the same upper bound on the integrality gap of the natural affine multicommodity LP relaxation.
\end{theorem}
```

The approximation factor is defined in `BuyAtBulk.Statements`. The small-instance
branch also includes the empty instance.

Source: [BuyAtBulk/Statements/OptimizedRounding.lean](BuyAtBulk/Statements/OptimizedRounding.lean).

<!-- lean-source: BuyAtBulk/Statements/OptimizedRounding.lean -->
```lean
noncomputable def optimizedFactor (h : ℕ) : ℝ :=
  if h ≤ 2 then 1 else (Real.log h) ^ 2 / (Real.log (Real.log h)) ^ 2
```

The main computational contract is in `BuyAtBulk.Computation.Runtime.Original`.
It concerns one actual graph-only program, `closedRun`, and its instrumented
execution, `closedTrace`. It requires no supplied fractional solution or LP oracle.
The constants and polynomial degrees are fixed independently of the instance.

Source: [BuyAtBulk/Computation/Runtime/OriginalPolynomial.lean](BuyAtBulk/Computation/Runtime/OriginalPolynomial.lean).

<!-- lean-source: BuyAtBulk/Computation/Runtime/OriginalPolynomial.lean -->
```lean
def PolynomialGraphApproximationTarget : Prop :=
  ∃ C d W e : ℕ, ∀ (n resources requests : ℕ) (tables : Tables n resources requests),
    (closedTrace tables).value=closedRun tables ∧
    ClosedSpec tables (closedTrace tables).value ∧
    (closedTrace tables).events.length≤C*(OriginalEncoding.inputSize tables+1)^d ∧
    WordsWithin (W*(OriginalEncoding.inputSize tables+1)^e) (closedTrace tables).events
```

Source: [BuyAtBulk/Main.lean](BuyAtBulk/Main.lean).

<!-- lean-source: BuyAtBulk/Main.lean -->
```lean
theorem polynomial_graph_approximation :
    Computation.Runtime.Original.PolynomialGraphApproximationTarget
```

`ClosedSpec` expands to the following correctness statement. Here `tables` is a
stored graph with `n` vertices, `resources` node/edge resources and `requests`
terminal pairs. Successful output covers every request, supports each returned
route with its bought flags, and compares its total cost with **every feasible
fractional solution**. This supplies the natural-LP integrality-gap upper bound.
An error identifies a disconnected request; an internal missing output is excluded.

Source: [BuyAtBulk/Computation/Runtime/OriginalProgram.lean](BuyAtBulk/Computation/Runtime/OriginalProgram.lean).

<!-- lean-source: BuyAtBulk/Computation/Runtime/OriginalProgram.lean -->
```lean
def ClosedSpec (result : Except (Fin requests) (StoredOriginalOutput tables)) : Prop :=
  SourceSpec tables (result.map some)
```

Source: [BuyAtBulk/Computation/Runtime/OriginalProgram.lean](BuyAtBulk/Computation/Runtime/OriginalProgram.lean).

<!-- lean-source: BuyAtBulk/Computation/Runtime/OriginalProgram.lean -->
```lean
def SourceSpec : Except (Fin requests) (Option (StoredOriginalOutput tables))→Prop
  | .error i=>
    ¬Nonempty (tables.graphData.graph.Path (tables.graphData.source i) (tables.graphData.target i)) ∧
      ¬Nonempty (OriginalPipeline.OriginalFractional tables.graphData)
  | .ok none=>False
  | .ok (some output)=>
    (output.routes.map fun e=>e.1).Perm (List.finRange requests) ∧
    (∀ e∈output.routes,∀ a,OriginalPipeline.usesResource tables.graphData e.1 e.2 a=true → output.bought[a.val]=true) ∧
    ∀ fractional : OriginalPipeline.OriginalFractional tables.graphData,
      ((outputBuying tables output+outputRental tables output : ℚ) : ℝ) ≤
        2500000000*Statements.optimizedFactor requests*
          (OriginalPipeline.buyingBudget tables.graphData fractional+OriginalPipeline.rentalBudget tables.graphData fractional)
```

The integral-comparator specialization states the approximation guarantee directly.
`IntegralInput tables` contains bought-resource flags and a supported original
path for every request; `input.buying + input.rental` is its total objective.

Source: [BuyAtBulk/Computation/Runtime/OriginalIntegral.lean](BuyAtBulk/Computation/Runtime/OriginalIntegral.lean).

<!-- lean-source: BuyAtBulk/Computation/Runtime/OriginalIntegral.lean -->
```lean
def IntegralGraphApproximationTarget : Prop :=
  ∀ (n resources requests : ℕ) (tables : Tables n resources requests),
    (∀ (output : StoredOriginalOutput tables), closedRun tables=.ok output →
      ∀ input : IntegralInput tables,
      ((outputBuying tables output+outputRental tables output : ℚ) : ℝ) ≤
        2500000000*Statements.optimizedFactor requests*(input.buying+input.rental)) ∧
    (∀ i : Fin requests, closedRun tables=.error i → ¬Nonempty (IntegralInput tables))
```

Source: [BuyAtBulk/Main.lean](BuyAtBulk/Main.lean).

<!-- lean-source: BuyAtBulk/Main.lean -->
```lean
theorem integral_graph_approximation :
    Computation.Runtime.Original.IntegralGraphApproximationTarget
```

The explicit constant `2500000000` witnesses the paper's absolute big-O constant.
Original node and edge costs are both represented by the resource table. Costs
are those of the actual returned routes and purchases. Polynomial runtime means
rational/integer word-operation counts and intermediate binary word lengths in
the full graph-input encoding; it does not assert compiled machine-instruction
correctness. The formal guarantee is assembled from these declarations rather
than expressed as a literal single-statement transcription of the paper.

# Edge-only LP integrality gap

Note: *An Ω(log h / log log h) Natural-LP Gap for Edge-Only Nonuniform
Buy-at-Bulk* (5 November 2026), Theorem 1. The note is distributed as a PDF and
is not bundled with this repository; its statement, transcribed from the PDF:

> There is an infinite sequence of undirected edge-only instances, with h → ∞
> unit-demand requests and supply size polynomial in h, such that
> OPT_integral / LP ≥ c · log h / log log h for an absolute constant c > 0.
> Every edge can be required to have strictly positive rational buying price
> and physical length, with O(log h)-bit encodings. The terminal-pair graph can
> additionally be required to be a matching.

The instances are `BuyAtBulk.GraphData`, so the LP is the same natural affine
LP as above, with per-commodity opening constraints. `GapFamily` lists the
properties in order: unbounded request count; edge-only unit-demand instances
with matching terminals and strictly positive data; polynomially many vertices
and resources and `O(log h)`-bit coefficients; and the gap against the attained
real LP optimum, which equals the rational optimum `lp`.

Source: [BuyAtBulk/EdgeOnlyGap/Items/GapFamily.lean](BuyAtBulk/EdgeOnlyGap/Items/GapFamily.lean).

<!-- lean-source: BuyAtBulk/EdgeOnlyGap/Items/GapFamily.lean -->
```lean
def GapFamily (F : ℕ → BuyAtBulk.GraphData) : Prop :=
  (∀ M : ℕ, ∃ N : ℕ, ∀ k, N ≤ k → M ≤ (F k).requestCount) ∧
  (∀ k, EdgeOnlyInstance (F k) ∧ MatchingTerminals (F k) ∧
    (∀ a, 0 < (F k).buying a ∧ 0 < (F k).length a)) ∧
  (∃ C K B : ℕ, 0 < C ∧ ∀ k,
    Fintype.card (F k).Vertex ≤ C*((F k).requestCount)^K ∧
    (F k).resourceCount ≤ C*((F k).requestCount)^K ∧ CoefficientsBounded (F k) B) ∧
  (∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ k, N ≤ k →
    ∃ opt lp : ℚ, ExactOptima (F k) opt lp ∧ 0 < lp ∧
      realLPValue (F k).toInstance = (lp : ℝ) ∧
      0 < realLPValue (F k).toInstance ∧
      0 < Real.log (Real.log (F k).requestCount) ∧
      c * Real.log (F k).requestCount / Real.log (Real.log (F k).requestCount) ≤
        (opt:ℝ) / realLPValue (F k).toInstance)
```

`ExactOptima D opt lp` says that `opt` is the attained integral optimum, `lp` the
attained rational LP optimum, and `lp` is also the attained minimum and infimum
of the LP over real feasible flows.

Source: [BuyAtBulk/EdgeOnlyGap/Items/Optima.lean](BuyAtBulk/EdgeOnlyGap/Items/Optima.lean).

<!-- lean-source: BuyAtBulk/EdgeOnlyGap/Items/Optima.lean -->
```lean
def ExactOptima (D : BuyAtBulk.GraphData) (opt lp : ℚ) : Prop :=
  RationalExactOptima D opt lp ∧
  RealLPMinimum D.toInstance (lp : ℝ) ∧ realLPValue D.toInstance = (lp : ℝ)
```

Source: [BuyAtBulk/EdgeOnlyGap/Items/Theorem1.lean](BuyAtBulk/EdgeOnlyGap/Items/Theorem1.lean).

<!-- lean-source: BuyAtBulk/EdgeOnlyGap/Items/Theorem1.lean -->
```lean
theorem theorem1 : ∃ F : ℕ → BuyAtBulk.GraphData, GapFamily F
```

The result is exported as `EdgeGapTarget` and is one of the conjuncts of
`BuyAtBulk.paper_main`. A further conjunct, `EdgeGapStagesTarget`
(`BuyAtBulk.edge_gap_stages`), records the note's intermediate nonnegative-cost
gap (§5, ratio `g/8`) and zero-price pendant reduction (§6).

Source: [BuyAtBulk/TheoremStatements.lean](BuyAtBulk/TheoremStatements.lean).

<!-- lean-source: BuyAtBulk/TheoremStatements.lean -->
```lean
def EdgeGapTarget : Prop :=
  ∃ F : ℕ → GraphData, EdgeOnlyGap.GapFamily F
```

Source: [BuyAtBulk/Main.lean](BuyAtBulk/Main.lean).

<!-- lean-source: BuyAtBulk/Main.lean -->
```lean
theorem edge_lower_bound : EdgeGapTarget
```

The note assumes the Erdős–Sachs theorem; it is proved here in the weak form the
note uses, so `theorem1` depends only on the standard axioms.

Source: [BuyAtBulk/EdgeOnlyGap/Items/ErdosSachs.lean](BuyAtBulk/EdgeOnlyGap/Items/ErdosSachs.lean).

<!-- lean-source: BuyAtBulk/EdgeOnlyGap/Items/ErdosSachs.lean -->
```lean
theorem erdosSachs (d g : ℕ) (hd : 4 ≤ d) (hg : 4 ≤ g) :
    ∃ H : FiniteGraph, RegularBase H d g ∧ H.n ≤ 8 * d^g
```

The constant proved is `c = c₀/24` for the logarithmic-scale constant `c₀`; the
note's sharper ratio `g/8` is weakened to `g/24` by the positivity modifications.

# Checking the excerpts

Verify the Lean excerpts against the checked-in sources with:

```sh
python3 scripts/check_statement_snippets.py
```

To also compare the quoted paper statement with a local copy of its LaTeX source:

```sh
python3 scripts/check_statement_snippets.py --paper-dir /path/to/paper
```
