# Computation model

`Primitive.lean` defines the closed rational/integer word-operation vocabulary.
An event records its actual operand/result binary lengths. `scan` includes fixed
loop control and allocation of the current cell; materialized index lists,
array/path copies and variable-length traversals are charged separately.
Rational arithmetic, comparison and normalization are word operations. The
helper additionally exposes its raw signed integer arithmetic through
`RawBridge.lean`.

`OriginalProgram.closedRun` takes only stored original graph tables. It returns
an actual disconnected request or original typed paths and bought-resource
flags. `OriginalTrace.closedTrace` refines that same program. Its complete
operation and word bounds are proved in `OriginalRuntime.lean`.

`OriginalEncodingSize.lean` specifies the dimension headers, adjacency cells,
resource labels, request endpoints, and signed rational numerator/denominator
words. `OriginalPolynomial.lean` proves fixed polynomial count and word bounds
in this binary input length, together with correctness of the actual output.
`PolynomialBudget.lean` checks nonnegative fixed polynomial syntax and computes
its coefficient weight and degree. The reification tactics produce ordinary
kernel-checked equalities.

The optimizer lives in `../PolynomialLP/`. It implements rational feasibility,
exact objective recovery and coordinate recovery on bounded compact LPs.
Its public polynomial contract includes infeasibility detection and exact
minimization on the unit cube. There is no LP oracle or supplied fractional
solution in the original graph algorithm.

`ParameterizedPolynomial.lean` covers arbitrary rounding parameters, charging
their binary lengths. `OriginalIntegral.lean` specializes the fractional
comparison to every supported integral bought network, preserving both costs.

These are source-level rational-operation and encoding-length theorems.
Native compiler correctness and literal binary-machine instruction traces are
separate specifications. The revised paper uses the ordinary-core zero-rental parameter argument that
is already verified here; finite-array preprocessing adapters are explicit.

`SuppliedPolynomial.lean` exports the full supplied-original-path-LP rounding
contract. It reads weighted paths, computes their exact length metadata, runs
arbitrary binary parameters, and projects original outputs. `SuppliedEncoding.lean`
includes the graph, openings, full path list, rational weights, and parameters
in the binary input size. This direct entry point does not require sparsifying
the supplied path list. The standalone sparsification and computed-network
contracts are described below.

`SparseSuppliedPolynomial.lean` exports the standalone supplied-list aggregation
and sparse decomposition contract, including original resource feasibility and
nonincreasing costs. `ComputedNetwork.lean` interprets precisely the computed
purchase flags as a bought network and bounds shortest-distance rental.
