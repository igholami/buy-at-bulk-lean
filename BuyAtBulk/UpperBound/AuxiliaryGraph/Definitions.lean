import BuyAtBulk.UpperBound.AuxiliaryTrace
import BuyAtBulk.UpperBound.Girth.AuxiliaryEdges

namespace BuyAtBulk.UpperBound.AuxiliaryGraph
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Unordered auxiliary graph edge, retaining scale separately. -/
def key (edge : AuxiliaryEdge G) : Sym2 V := s(edge.source, edge.target)

/-- Actual simple graph supported by the stored auxiliary records at one
scale. Simplicity of the record list remains a theorem to prove, not a field. -/
def atScale (edges : List (AuxiliaryEdge G)) (scale : ℚ) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | ∃ record ∈ edges, record.scale = scale ∧ e = key record}

@[simp] theorem atScale_adj (edges : List (AuxiliaryEdge G)) (scale : ℚ) (u v : V) :
    (atScale edges scale).Adj u v ↔
      (∃ record ∈ edges, record.scale = scale ∧ s(u, v) = key record) ∧ u ≠ v := by
  rfl

@[simp] theorem atScale_nil (scale : ℚ) : atScale ([] : List (AuxiliaryEdge G)) scale = ⊥ := by
  ext u v
  simp [atScale_adj]

/-- The scale's graph vertices are the endpoints which actually occur,
without counting isolated vertices of the underlying physical graph. -/
noncomputable def activeVertices (edges : List (AuxiliaryEdge G)) (scale : ℚ) : Finset V := by
  classical
  exact (edges.filter fun edge => edge.scale = scale).toFinset.biUnion fun edge =>
    {edge.source, edge.target}

/-- Distinct graph vertices supported by sufficiently high center records. -/
noncomputable def eligibleVertices (records : List (CenterRecord V)) (scale : ℚ) : Finset V := by
  classical
  exact ((records.filter fun record => scale ≤ record.birthScale).map CenterRecord.endpoint).toFinset

@[simp] theorem eligibleVertices_mem (records : List (CenterRecord V)) (scale : ℚ) (v : V) :
    v ∈ eligibleVertices records scale ↔ EligibleCenter records v scale := by
  classical
  simp [eligibleVertices, EligibleCenter, and_assoc, and_comm, eq_comm]

end BuyAtBulk.UpperBound.AuxiliaryGraph
