import BuyAtBulk.UpperBound.NodeDistance
import BuyAtBulk.UpperBound.CenterRecords
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

/-! Concrete node-rounding program state. Auxiliary edges retain actual simple
physical realizations; no girth, packing, or cost conclusion is assumed. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

structure AuxiliaryEdge where
  source : V
  target : V
  scale : ℚ
  realization : G.Path source target

structure RoundingState where
  bought : Finset V
  centers : List (CenterRecord V)
  edges : List (AuxiliaryEdge G)

noncomputable def mixedNodeWeight (buying physical : V → ℚ)
    (state : RoundingState G) (allowance scale : ℚ) (v : V) : ℚ := by
  classical
  exact (if v ∈ state.bought then 0 else buying v) + (scale / allowance) * physical v

/-- Exactly the finite existential test for bought distance at most threshold,
with disconnected pairs making the test false. Rental costs never disappear. -/
def HasShortBoughtRoute (physical : V → ℚ) (state : RoundingState G)
    (u v : V) (threshold : ℚ) : Prop :=
  ∃ path : G.Path u v, path.val.support.toFinset ⊆ state.bought ∧
    NodeMetric.walkWeight G physical path.val ≤ threshold

/-- The center-search test ranges over actual physical endpoints and paths. -/
def NearEligibleCenter (buying physical : V → ℚ) (state : RoundingState G)
    (allowance scale : ℚ) (z u : V) : Prop :=
  EligibleCenter state.centers u scale ∧
    ∃ path : G.Path z u,
      NodeMetric.walkWeight G (mixedNodeWeight G buying physical state allowance scale) path.val ≤ scale / 8

/-- Buy precisely the nodes of an actual path, retaining all prior resources. -/
noncomputable def buyPath (state : RoundingState G) {u v : V} (path : G.Path u v) : RoundingState G := by
  classical
  exact { state with bought := state.bought ∪ path.val.support.toFinset }

def recordBirth (state : RoundingState G) (vertex : V) (scale : ℚ) : RoundingState G :=
  { state with centers := ⟨vertex, scale⟩ :: state.centers }

def recordEdge (state : RoundingState G) {u v : V} (path : G.Path u v) (scale : ℚ) : RoundingState G :=
  { state with edges := ⟨u, v, scale, path⟩ :: state.edges }

/-- A stored auxiliary edge really is available in the current bought graph. -/
def EdgeRealizationsBought (state : RoundingState G) : Prop :=
  ∀ edge ∈ state.edges, edge.realization.val.support.toFinset ⊆ state.bought

theorem bought_subset_buyPath (state : RoundingState G) {u v : V} (path : G.Path u v) :
    state.bought ⊆ (buyPath G state path).bought := by
  classical
  exact Finset.subset_union_left

theorem path_bought_buyPath (state : RoundingState G) {u v : V} (path : G.Path u v) :
    path.val.support.toFinset ⊆ (buyPath G state path).bought := by
  classical
  exact Finset.subset_union_right

theorem edgeRealizationsBought_buyPath (state : RoundingState G)
    (supported : EdgeRealizationsBought G state) {u v : V} (path : G.Path u v) :
    EdgeRealizationsBought G (buyPath G state path) := by
  intro edge member
  exact (supported edge member).trans (bought_subset_buyPath G state path)

theorem edgeRealizationsBought_recordBirth (state : RoundingState G)
    (supported : EdgeRealizationsBought G state) (vertex : V) (scale : ℚ) :
    EdgeRealizationsBought G (recordBirth G state vertex scale) := supported

theorem edgeRealizationsBought_recordEdge (state : RoundingState G)
    (supported : EdgeRealizationsBought G state) {u v : V} (path : G.Path u v) (scale : ℚ)
    (path_bought : path.val.support.toFinset ⊆ state.bought) :
    EdgeRealizationsBought G (recordEdge G state path scale) := by
  intro edge member
  cases List.mem_cons.mp member with
  | inl heq => subst edge; exact path_bought
  | inr old => exact supported edge old

end BuyAtBulk.UpperBound
