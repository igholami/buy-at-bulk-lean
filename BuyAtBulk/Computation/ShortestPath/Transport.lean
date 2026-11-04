import BuyAtBulk.Computation.ShortestPath.Encoding

/-! The executable indexed metric refines the existing metric on any finite
graph once an explicit vertex numbering is supplied. -/
namespace BuyAtBulk.Computation.ShortestPath

variable {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}

def copyPath {u v u' v' : V} (path : G.Path u v) (source_eq : u = u') (target_eq : v = v') : G.Path u' v' :=
  ⟨path.val.copy source_eq target_eq, (path.val.isPath_copy source_eq target_eq).mpr path.property⟩

theorem copyPath_weight (weight : V → ℚ) {u v u' v' : V} (path : G.Path u v)
    (source_eq : u = u') (target_eq : v = v') :
    NodeMetric.walkWeight G weight (copyPath path source_eq target_eq).val =
      NodeMetric.walkWeight G weight path.val := by
  subst u'
  subst v'
  rfl

theorem map_walkWeight (iso : G ≃g H) (weight : W → ℚ) {u v : V} (walk : G.Walk u v) :
    NodeMetric.walkWeight H weight (walk.map iso.toHom) =
      NodeMetric.walkWeight G (fun x => weight (iso x)) walk := by
  classical
  unfold NodeMetric.walkWeight
  rw [SimpleGraph.Walk.support_map]
  have supports : (List.map (⇑iso.toHom) walk.support).toFinset = walk.support.toFinset.image iso.toHom := by
    ext x
    simp
  rw [supports]
  exact Finset.sum_image (g := iso.toHom) (f := weight) (fun _ _ _ _ same => iso.injective same)

theorem distance_iso [Fintype V] [Fintype W] (iso : G ≃g H) (weight : W → ℚ)
    (source target : V) (original_reachable : Nonempty (G.Path source target))
    (encoded_reachable : Nonempty (H.Path (iso source) (iso target))) :
    NodeMetric.distance H weight (iso source) (iso target) encoded_reachable =
      NodeMetric.distance G (fun x => weight (iso x)) source target original_reachable := by
  apply le_antisymm
  · obtain ⟨path, shortest⟩ := NodeMetric.exists_shortest G (fun x => weight (iso x)) original_reachable
    calc
      _ ≤ NodeMetric.walkWeight H weight (path.map iso.toHom iso.injective).val := NodeMetric.distance_le_path H weight encoded_reachable _
      _ = NodeMetric.walkWeight G (fun x => weight (iso x)) path.val := map_walkWeight iso weight path.val
      _ = _ := shortest
  · obtain ⟨path, shortest⟩ := NodeMetric.exists_shortest H weight encoded_reachable
    let back := copyPath (path.map iso.symm.toHom iso.symm.injective)
      (iso.symm_apply_apply source) (iso.symm_apply_apply target)
    calc
      _ ≤ NodeMetric.walkWeight G (fun x => weight (iso x)) back.val := NodeMetric.distance_le_path G _ original_reachable _
      _ = NodeMetric.walkWeight H weight path.val := by
        rw [copyPath_weight]
        change NodeMetric.walkWeight G (fun x => weight (iso x)) (path.val.map iso.symm.toHom) = _
        rw [map_walkWeight]
        simp only [iso.apply_symm_apply]
      _ = _ := shortest

variable {n : ℕ}

def indexedDistances (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℚ)
    (numbering : V ≃ Fin n) (target : V) : Vector (WithTop ℚ) n :=
  shortestDistances (GraphEncoding.ofGraph G numbering).graph
    (fun i => weight (numbering.symm i)) (numbering target)

theorem indexedDistances_correct [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℚ) (nonneg : ∀ v, 0 ≤ weight v) (numbering : V ≃ Fin n)
    (source target : V) (reachable : Nonempty (G.Path source target)) :
    (indexedDistances G weight numbering target)[(numbering source).val] =
      (NodeMetric.distance G weight source target reachable : WithTop ℚ) := by
  let iso := GraphEncoding.ofGraphIso G numbering
  have encoded_reachable : Nonempty ((GraphEncoding.ofGraph G numbering).graph.Path (numbering source) (numbering target)) :=
    ⟨reachable.some.map iso.toHom iso.injective⟩
  have correct := shortestDistances_eq_distance (GraphEncoding.ofGraph G numbering).graph
    (fun i => weight (numbering.symm i)) (fun i => nonneg (numbering.symm i))
    (numbering source) (numbering target) encoded_reachable
  have metric := distance_iso iso (fun i => weight (numbering.symm i)) source target reachable encoded_reachable
  have metric' : NodeMetric.distance (GraphEncoding.ofGraph G numbering).graph
      (fun i => weight (numbering.symm i)) (numbering source) (numbering target) encoded_reachable =
        NodeMetric.distance G weight source target reachable := by
    change NodeMetric.distance (GraphEncoding.ofGraph G numbering).graph
      (fun i => weight (numbering.symm i)) (numbering source) (numbering target) encoded_reachable =
        NodeMetric.distance G (fun x => weight (numbering.symm (numbering x))) source target reachable at metric
    simpa only [Equiv.symm_apply_apply] using metric
  exact correct.trans (congrArg (fun q : ℚ => (q : WithTop ℚ)) metric')

end BuyAtBulk.Computation.ShortestPath
