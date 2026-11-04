import BuyAtBulk.Computation.Attachment.Primitives

/-! Deterministic shortest-route threshold tests. Bought-route tests use a
penalty larger than the threshold for every unbought node; exact equivalence
is proved, including zero-length paths at unbought endpoints. -/
namespace BuyAtBulk.Computation.Attachment
open BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

def shortRoute (weight : V → ℚ) (source target : V) (threshold : ℚ) : Option (G.Path source target) :=
  match ShortestPath.indexedPath G weight numbering source target with
  | none => none
  | some path => if pathCost G weight path ≤ threshold then some path else none

theorem shortestPath_shortest (weight : V → ℚ) (nonneg : ∀ v, 0 ≤ weight v)
    {source target : V} (path : G.Path source target)
    (returned : ShortestPath.indexedPath G weight numbering source target = some path) : IsShortest G weight path := by
  obtain ⟨actual, computed, cost, _⟩ := ShortestPath.indexed_shortest_path G weight nonneg numbering source target ⟨path⟩
  have same : path = actual := Option.some.inj (returned.symm.trans computed)
  subst actual
  intro other
  rw [cost]
  exact NodeMetric.distance_le_path G weight ⟨path⟩ other

theorem shortRoute_some (weight : V → ℚ) (nonneg : ∀ v, 0 ≤ weight v)
    {source target : V} {threshold : ℚ} (path : G.Path source target)
    (returned : shortRoute G numbering weight source target threshold = some path) :
    IsShortest G weight path ∧ NodeMetric.walkWeight G weight path.val ≤ threshold := by
  unfold shortRoute at returned
  split at returned
  · contradiction
  · rename_i actual computed
    split at returned
    · rename_i short
      have same := Option.some.inj returned
      subst path
      exact ⟨shortestPath_shortest G numbering weight nonneg actual computed, (pathCost_eq G weight actual) ▸ short⟩
    · contradiction

theorem shortRoute_exists (weight : V → ℚ) (nonneg : ∀ v, 0 ≤ weight v)
    {source target : V} {threshold : ℚ}
    (witness : ∃ path : G.Path source target, NodeMetric.walkWeight G weight path.val ≤ threshold) :
    ∃ path, shortRoute G numbering weight source target threshold = some path := by
  obtain ⟨candidate, short⟩ := witness
  obtain ⟨path, computed, cost, _⟩ := ShortestPath.indexed_shortest_path G weight nonneg numbering source target ⟨candidate⟩
  have bounded : pathCost G weight path ≤ threshold := by
    rw [pathCost_eq, cost]
    exact (NodeMetric.distance_le_path G weight ⟨candidate⟩ candidate).trans short
  exact ⟨path, by simp only [shortRoute, computed, if_pos bounded]⟩

theorem shortRoute_none_iff (weight : V → ℚ) (nonneg : ∀ v, 0 ≤ weight v)
    (source target : V) (threshold : ℚ) :
    shortRoute G numbering weight source target threshold = none ↔
      ¬ ∃ path : G.Path source target, NodeMetric.walkWeight G weight path.val ≤ threshold := by
  constructor
  · intro missing witness
    obtain ⟨path, returned⟩ := shortRoute_exists G numbering weight nonneg witness
    rw [missing] at returned
    contradiction
  · intro no_route
    cases returned : shortRoute G numbering weight source target threshold with
    | none => rfl
    | some path => exact False.elim (no_route ⟨path, (shortRoute_some G numbering weight nonneg path returned).2⟩)

def boughtWeight (physical : V → ℚ) (state : RoundingState G) (threshold : ℚ) (v : V) : ℚ :=
  physical v + if v ∈ state.bought then 0 else max threshold 0 + 1

theorem boughtWeight_nonneg (physical : V → ℚ) (nonneg : ∀ v, 0 ≤ physical v)
    (state : RoundingState G) (threshold : ℚ) : ∀ v, 0 ≤ boughtWeight G physical state threshold v := by
  intro v
  unfold boughtWeight
  apply add_nonneg (nonneg v)
  split
  · exact le_rfl
  · have bound : (0 : ℚ) ≤ max threshold 0 := le_max_right _ _
    linarith

theorem boughtWeight_supported (physical : V → ℚ) (state : RoundingState G) (threshold : ℚ)
    {source target : V} (path : G.Path source target) (supported : path.val.support.toFinset ⊆ state.bought) :
    pathCost G (boughtWeight G physical state threshold) path = pathCost G physical path := by
  rw [pathCost_eq, pathCost_eq]
  unfold NodeMetric.walkWeight
  apply Finset.sum_congr rfl
  intro v member
  have bought : v ∈ state.bought := supported (by simpa only [List.mem_toFinset] using member)
  simp only [boughtWeight, if_pos bought, add_zero]

theorem boughtWeight_short_supported (physical : V → ℚ) (nonneg : ∀ v, 0 ≤ physical v)
    (state : RoundingState G) (threshold : ℚ) {source target : V} (path : G.Path source target)
    (short : pathCost G (boughtWeight G physical state threshold) path ≤ threshold) :
    path.val.support.toFinset ⊆ state.bought := by
  intro v member
  by_contra missing
  have term := node_le_pathCost G (boughtWeight G physical state threshold)
    (boughtWeight_nonneg G physical nonneg state threshold) path v (List.mem_toFinset.mp member)
  unfold boughtWeight at term
  rw [if_neg missing] at term
  change physical v + (max threshold 0 + 1) ≤ pathCost G (boughtWeight G physical state threshold) path at term
  have bound : threshold ≤ max threshold 0 := le_max_left _ _
  linarith [nonneg v]

def boughtRoute (physical : V → ℚ) (state : RoundingState G)
    (source target : V) (threshold : ℚ) : Option (G.Path source target) :=
  shortRoute G numbering (boughtWeight G physical state threshold) source target threshold

theorem boughtRoute_some (physical : V → ℚ) (nonneg : ∀ v, 0 ≤ physical v)
    (state : RoundingState G) {source target : V} {threshold : ℚ} (path : G.Path source target)
    (returned : boughtRoute G numbering physical state source target threshold = some path) :
    path.val.support.toFinset ⊆ state.bought ∧ NodeMetric.walkWeight G physical path.val ≤ threshold := by
  have short := (shortRoute_some G numbering _ (boughtWeight_nonneg G physical nonneg state threshold) path returned).2
  rw [← pathCost_eq] at short
  have supported := boughtWeight_short_supported G physical nonneg state threshold path short
  refine ⟨supported, ?_⟩
  rw [boughtWeight_supported G physical state threshold path supported, pathCost_eq] at short
  exact short

theorem boughtRoute_none_iff (physical : V → ℚ) (nonneg : ∀ v, 0 ≤ physical v)
    (state : RoundingState G) (source target : V) (threshold : ℚ) :
    boughtRoute G numbering physical state source target threshold = none ↔
      ¬ HasShortBoughtRoute G physical state source target threshold := by
  constructor
  · intro missing witness
    obtain ⟨path, supported, short⟩ := witness
    have weighted : NodeMetric.walkWeight G (boughtWeight G physical state threshold) path.val ≤ threshold := by
      rw [← pathCost_eq, boughtWeight_supported G physical state threshold path supported, pathCost_eq]
      exact short
    exact (shortRoute_none_iff G numbering _ (boughtWeight_nonneg G physical nonneg state threshold) source target threshold).mp missing ⟨path, weighted⟩
  · intro no_route
    cases returned : boughtRoute G numbering physical state source target threshold with
    | none => rfl
    | some path => exact False.elim (no_route ⟨path, boughtRoute_some G numbering physical nonneg state path returned⟩)

theorem boughtRoute_shortest (physical : V → ℚ) (nonneg : ∀ v, 0 ≤ physical v)
    (state : RoundingState G) {source target : V} {threshold : ℚ} (path : G.Path source target)
    (returned : boughtRoute G numbering physical state source target threshold = some path) :
    ∀ other : G.Path source target, other.val.support.toFinset ⊆ state.bought →
      NodeMetric.walkWeight G physical path.val ≤ NodeMetric.walkWeight G physical other.val := by
  intro other other_supported
  have supported := (boughtRoute_some G numbering physical nonneg state path returned).1
  have shortest := (shortRoute_some G numbering _ (boughtWeight_nonneg G physical nonneg state threshold) path returned).1 other
  rw [← pathCost_eq, ← pathCost_eq, boughtWeight_supported G physical state threshold path supported,
    boughtWeight_supported G physical state threshold other other_supported, pathCost_eq, pathCost_eq] at shortest
  exact shortest

end BuyAtBulk.Computation.Attachment
