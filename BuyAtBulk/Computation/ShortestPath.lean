import BuyAtBulk.Computation.ShortestPath.Transport

/-! Executable shortest paths for explicitly numbered finite graphs. Distance
and actual path outputs refine the paper's metric, with polynomial scheduled
rational-operation bounds. Bit complexity is a separate property. -/
namespace BuyAtBulk.Computation.ShortestPath

variable {V : Type} {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℚ)

def indexedPath (numbering : V ≃ Fin n) (source target : V) : Option (G.Path source target) :=
  let iso := GraphEncoding.ofGraphIso G numbering
  (shortestPath (GraphEncoding.ofGraph G numbering).graph (fun i => weight (numbering.symm i))
    (numbering source) (numbering target)).map fun path =>
      copyPath (path.map iso.symm.toHom iso.symm.injective)
        (iso.symm_apply_apply source) (iso.symm_apply_apply target)

/-- Concrete shortest-path refinement: compute a distance and an actual simple
path without enumerating paths. The counters cover respectively distance
relaxations and recovery including its recomputed tables and predecessor scans. -/
theorem indexed_shortest_path [Fintype V] (nonneg : ∀ v, 0 ≤ weight v)
    (numbering : V ≃ Fin n) (source target : V) (reachable : Nonempty (G.Path source target)) :
    ∃ path : G.Path source target,
      indexedPath G weight numbering source target = some path ∧
      NodeMetric.walkWeight G weight path.val = NodeMetric.distance G weight source target reachable ∧
      (indexedDistances G weight numbering target)[(numbering source).val] =
        (NodeMetric.distance G weight source target reachable : WithTop ℚ) ∧
      (countedIterate (GraphEncoding.ofGraph G numbering).graph (fun i => weight (numbering.symm i))
        (numbering target) n).2 = n ^ 3 ∧
      (recoverScheduled (GraphEncoding.ofGraph G numbering).graph (fun i => weight (numbering.symm i))
        (numbering target) n (numbering source)).2 ≤ n ^ 4 + n ^ 2 + n := by
  let input := GraphEncoding.ofGraph G numbering
  let iso := GraphEncoding.ofGraphIso G numbering
  let weights := Vector.ofFn fun i => weight (numbering.symm i)
  have encoded_reachable : Nonempty (input.graph.Path (numbering source) (numbering target)) :=
    ⟨reachable.some.map iso.toHom iso.injective⟩
  obtain ⟨encoded, returned, encoded_cost, distance_count, recovery_count⟩ := input.encoded_shortest_path weights
    (fun i => by simpa [weights] using nonneg (numbering.symm i)) (numbering source) (numbering target) encoded_reachable
  let path := copyPath (encoded.map iso.symm.toHom iso.symm.injective)
    (iso.symm_apply_apply source) (iso.symm_apply_apply target)
  have metric := distance_iso iso (fun i => weight (numbering.symm i)) source target reachable encoded_reachable
  have metric' : NodeMetric.distance input.graph (fun i => weight (numbering.symm i))
      (numbering source) (numbering target) encoded_reachable = NodeMetric.distance G weight source target reachable := by
    change NodeMetric.distance input.graph (fun i => weight (numbering.symm i))
      (numbering source) (numbering target) encoded_reachable =
        NodeMetric.distance G (fun x => weight (numbering.symm (numbering x))) source target reachable at metric
    simpa only [Equiv.symm_apply_apply] using metric
  have weights_eq : (fun i => weights[i.val]) = fun i => weight (numbering.symm i) := by
    funext i
    simp [weights]
  unfold GraphEncoding.path at returned
  rw [weights_eq] at returned encoded_cost distance_count recovery_count
  refine ⟨path, ?_, ?_, indexedDistances_correct G weight nonneg numbering source target reachable,
    distance_count, recovery_count⟩
  · change Option.map _ (shortestPath input.graph (fun i => weight (numbering.symm i)) (numbering source) (numbering target)) = _
    rw [returned]
    rfl
  · have copied := copyPath_weight weight (encoded.map iso.symm.toHom iso.symm.injective)
      (iso.symm_apply_apply source) (iso.symm_apply_apply target)
    have mapped := map_walkWeight iso.symm weight encoded.val
    exact copied.trans (mapped.trans (encoded_cost.trans metric'))


/-- The executable option result also decides disconnection exactly. -/
theorem indexedPath_none_iff [Fintype V] (nonneg : ∀ v, 0 ≤ weight v)
    (numbering : V ≃ Fin n) (source target : V) :
    indexedPath G weight numbering source target = none ↔ ¬ Nonempty (G.Path source target) := by
  constructor
  · intro missing reachable
    obtain ⟨path, returned, _⟩ := indexed_shortest_path G weight nonneg numbering source target reachable
    rw [missing] at returned
    contradiction
  · intro disconnected
    cases result : indexedPath G weight numbering source target with
    | none => rfl
    | some path => exact False.elim (disconnected ⟨path⟩)

end BuyAtBulk.Computation.ShortestPath
