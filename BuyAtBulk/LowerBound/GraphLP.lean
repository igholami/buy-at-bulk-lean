import BuyAtBulk.LowerBound.RepeatedRequests
import BuyAtBulk.Model.GraphInstance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace BuyAtBulk.LowerBound
open scoped BigOperators

/-- The lower-bound graph, with exactly `h` commodity occurrences. Only its
`2k` paid nodes are resources; all omitted nodes and edges are free. -/
noncomputable abbrev graphData (k h : ℕ) (request : Fin h → Request k) : GraphData where
  Vertex := Vertex k
  vertexFintype := inferInstance
  graph := graph k
  resourceCount := 2 * k
  requestCount := h
  source := fun _ => .root
  target := fun i => .terminal (request i)
  location := fun j => Sum.inl (.paid j)
  location_injective := by intro a b hab; simpa using hab
  location_valid := by intro a; trivial
  buying := fun _ => 1
  length := fun _ => 0
  demand := fun _ => 1
  buying_nonneg := by intro a; norm_num
  length_nonneg := by intro a; norm_num
  demand_pos := by intro i; norm_num

/-- The two-edge simple path through a member of the request subset. -/
def shortPath (k : ℕ) (A : Request k) (j : A.val) :
    (graph k).Path .root (.terminal A) :=
  ⟨.cons (show (graph k).Adj .root (.paid j.val) from trivial)
    (.cons (show (graph k).Adj (.paid j.val) (.terminal A) from j.property) .nil),
    SimpleGraph.Walk.IsPath.mk' (by simp)⟩

@[simp] theorem shortPath_support (k : ℕ) (A : Request k) (j : A.val) :
    (shortPath k A j).val.support = [.root, .paid j.val, .terminal A] := rfl

@[simp] theorem shortPath_resources (k h : ℕ) (request : Fin h → Request k)
    (i : Fin h) (j : (request i).val) :
    (graphData k h request).pathResources ⟨i, shortPath k (request i) j⟩ = {j.val} := by
  classical
  ext a
  simp [GraphData.pathResources, graphData, shortPath_support]

/-- Uniformly split each occurrence's unit flow among its `k` direct paths. -/
noncomputable def uniformSolution (k h : ℕ) (request : Fin h → Request k) :
    (graphData k h request).toInstance.FractionalSolution where
  opening := fun _ => 1 / (k : ℚ)
  flow := fun i p => ∑ j : (request i).val,
    if (graphData k h request).encode i (shortPath k (request i) j) = p
      then 1 / (k : ℚ) else 0

end BuyAtBulk.LowerBound
