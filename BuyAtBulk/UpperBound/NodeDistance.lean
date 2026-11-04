import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith

/-! Original node-weight shortest paths used by the fixed toll construction.
Distances include both endpoints. All minima range over actual simple graph paths. -/
namespace BuyAtBulk.NodeMetric

variable {V : Type} [Fintype V] (G : SimpleGraph V) (weight : V → ℚ)

noncomputable def walkWeight {u v : V} (walk : G.Walk u v) : ℚ := by
  classical
  exact ∑ a ∈ walk.support.toFinset, weight a

noncomputable def distance (u v : V) (reachable : Nonempty (G.Path u v)) : ℚ := by
  classical
  exact (Finset.univ.image fun path : G.Path u v => walkWeight G weight path.val).min'
    ⟨_, Finset.mem_image.mpr ⟨reachable.some, Finset.mem_univ _, rfl⟩⟩

theorem distance_le_path {u v : V} (reachable : Nonempty (G.Path u v))
    (path : G.Path u v) : distance G weight u v reachable ≤ walkWeight G weight path.val := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨path, Finset.mem_univ _, rfl⟩)

theorem exists_shortest {u v : V} (reachable : Nonempty (G.Path u v)) :
    ∃ path : G.Path u v, walkWeight G weight path.val = distance G weight u v reachable := by
  classical
  have hm := Finset.min'_mem
    (Finset.univ.image fun path : G.Path u v => walkWeight G weight path.val)
    (show (Finset.univ.image fun path : G.Path u v => walkWeight G weight path.val).Nonempty from
      ⟨_, Finset.mem_image.mpr ⟨reachable.some, Finset.mem_univ _, rfl⟩⟩)
  obtain ⟨path, _, heq⟩ := Finset.mem_image.mp hm
  exact ⟨path, heq⟩

omit [Fintype V] in
theorem toPath_weight_le [DecidableEq V] (nonneg : ∀ v, 0 ≤ weight v) {u v : V}
    (walk : G.Walk u v) : walkWeight G weight walk.toPath.val ≤ walkWeight G weight walk := by
  unfold walkWeight
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro a ha
    have ha' : a ∈ walk.toPath.val.support := by simpa only [List.mem_toFinset] using ha
    have hs := walk.support_toPath_subset_support ha'
    simpa only [List.mem_toFinset] using hs
  · intro a _ _
    exact nonneg a

theorem endpoint_le_distance (nonneg : ∀ v, 0 ≤ weight v) {u v : V}
    (reachable : Nonempty (G.Path u v)) : weight v ≤ distance G weight u v reachable := by
  classical
  obtain ⟨path, heq⟩ := exists_shortest G weight reachable
  rw [← heq]
  unfold walkWeight
  apply Finset.single_le_sum (fun a _ => nonneg a)
  exact List.mem_toFinset.mpr path.val.end_mem_support

omit [Fintype V] in
theorem concat_weight_le [DecidableEq V] (nonneg : ∀ v, 0 ≤ weight v) {s u v : V}
    (walk : G.Walk s u) (edge : G.Adj u v) :
    walkWeight G weight (walk.concat edge) ≤ walkWeight G weight walk + weight v := by
  let : DecidableEq V := Classical.decEq V
  have support_eq : (walk.concat edge).support.toFinset = insert v walk.support.toFinset := by
    ext a
    simp
  unfold walkWeight
  rw [support_eq]
  by_cases hv : v ∈ walk.support.toFinset
  · rw [Finset.insert_eq_of_mem hv]
    exact le_add_of_nonneg_right (nonneg v)
  · rw [Finset.sum_insert hv]
    exact le_of_eq (add_comm _ _)

theorem distance_prefix (nonneg : ∀ v, 0 ≤ weight v) {s u v : V}
    (reachable_u : Nonempty (G.Path s u)) (reachable_v : Nonempty (G.Path s v))
    (edge : G.Adj u v) :
    distance G weight s v reachable_v ≤ distance G weight s u reachable_u + weight v := by
  classical
  obtain ⟨path, heq⟩ := exists_shortest G weight reachable_u
  calc
    _ ≤ walkWeight G weight (path.val.concat edge).toPath.val := distance_le_path G weight _ _
    _ ≤ walkWeight G weight (path.val.concat edge) := toPath_weight_le G weight nonneg _
    _ ≤ walkWeight G weight path.val + weight v := concat_weight_le G weight nonneg _ edge
    _ = _ := by rw [heq]

theorem distance_self (nonneg : ∀ v, 0 ≤ weight v) (s : V)
    (reachable : Nonempty (G.Path s s)) : distance G weight s s reachable = weight s := by
  apply le_antisymm
  · have h := distance_le_path G weight reachable (SimpleGraph.Path.nil : G.Path s s)
    simpa [walkWeight, SimpleGraph.Path.nil] using h
  · exact endpoint_le_distance G weight nonneg reachable

end BuyAtBulk.NodeMetric
