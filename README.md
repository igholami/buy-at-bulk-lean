# Buy-at-Bulk in Lean

Lean 4 formalization of a deterministic polynomial-time
O(log² h / (log log h)²) approximation for undirected nonuniform buy-at-bulk
network design, with a constant factor for at most two requests. The result
allows positive rational demands and nonnegative rational buying prices and
physical lengths on both nodes and edges.

The graph-only algorithm computes its fractional solution and returns original
paths and bought-resource flags, or identifies a disconnected request. Its cost
bound holds against every feasible fractional solution and every integral
comparator, establishing both the approximation guarantee and the natural-LP
integrality-gap upper bound.

All proofs are complete, with no `sorry` or custom axioms. The audited theorem
dependencies use only `propext`, `Classical.choice`, and `Quot.sound`.

## Main statements

- [Statement review](statements.md): the paper's main approximation statement,
  exact Lean contracts, and their correspondence.
- [Public theorems](BuyAtBulk/Main.lean): `polynomial_graph_approximation` gives
  correctness and polynomial operation/word bounds for the computed graph-only
  program; `integral_graph_approximation` states its integral comparison.
- [Graph-only program](BuyAtBulk/Computation/Runtime/OriginalProgram.lean):
  `closedRun` and its correctness predicate.
- [Polynomial contract](BuyAtBulk/Computation/Runtime/OriginalPolynomial.lean):
  fixed global bounds in the complete binary graph-input encoding.

The library also contains separate-budget parameterized rounding, sparse
supplied-path decomposition, an exact rational LP optimizer, and a logarithmic
node-cost LP lower bound. `BuyAtBulk.paper_main` combines the public results.

Runtime is formalized in the rational/integer word-operation model defined in
[Primitive.lean](BuyAtBulk/Computation/Runtime/Primitive.lean), with polynomial
binary lengths for every recorded intermediate word. These are source-level
operation and encoding bounds; native compiler and machine-instruction
correctness are outside this model. Finite representations and deterministic
tie choices need not be identical to the paper's presentation.

## Build and audit

Install Lean using elan, then run from the repository root:

```sh
lake exe cache get
lake build BuyAtBulk
python3 scripts/check_axioms.py
python3 scripts/check_dependencies.py
python3 scripts/check_statement_snippets.py
for test in tests/*.lean; do
  lake env lean -DautoImplicit=false "$test" || exit 1
done
```

The Lean toolchain and mathlib dependency are pinned in `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json`. Python 3 is required for the audits.

The axiom audit checks every project theorem, including private helpers, and
rejects unfinished proofs, custom axioms and unchecked declarations. The
dependency audit verifies that every library module occurs in the elaborated
type/value dependency closure of `BuyAtBulk.paper_main`; imports alone do not
count. The statement check verifies that documented Lean excerpts match their
source. See [AUDIT.txt](AUDIT.txt) and [PROOF_STATUS.txt](PROOF_STATUS.txt) for the
verification record.

## Structure

- `BuyAtBulk/Model/`: graph/resource models, LP formulations and reductions.
- `BuyAtBulk/UpperBound/`: rounding, packing, girth and cost analysis.
- `BuyAtBulk/LowerBound/`: node-cost integrality-gap construction.
- `BuyAtBulk/Computation/`: executable algorithms, exact LP optimization and
  runtime proofs.
- `BuyAtBulk/Statements/`: public mathematical predicates and transports.
- `tests/`: guarded execution regressions.
- `scripts/`: reproducible source, axiom and dependency checks.
