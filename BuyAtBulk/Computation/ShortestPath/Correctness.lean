import BuyAtBulk.Computation.ShortestPath.Algorithm

/-! Correctness is derived from the recurrence: every finite label is an
actual walk cost, and every walk with at most k edges bounds the k-round label.
Nonnegative cycle erasure then identifies the result with the existing metric. -/
namespace BuyAtBulk.Computation.ShortestPath

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (weight : Fin n → ℚ)

def Sound (target : Fin n) (table : Vector (WithTop ℚ) n) : Prop :=
  ∀ (v : Fin n) (q : ℚ), table[v.val] = (q : WithTop ℚ) →
    ∃ walk : G.Walk v target, traversalCost G weight walk = q

theorem initial_sound (target : Fin n) : Sound G weight target (initial weight target) := by
  intro v q value
  rw [initial_get] at value
  by_cases same : v = target
  · subst v
    simp only [ite_true, WithTop.coe_inj] at value
    exact ⟨.nil, value⟩
  · simp [same] at value

theorem step_sound (target : Fin n) (old : Vector (WithTop ℚ) n)
    (sound : Sound G weight target old) : Sound G weight target (step G weight old) := by
  intro v q value
  rw [step_get] at value
  by_cases stay : old[v.val] ≤ Finset.univ.inf (candidate G weight old v)
  · rw [min_eq_left stay] at value
    exact sound v q value
  · rw [min_eq_right (le_of_not_ge stay)] at value
    obtain ⟨u, _, chosen⟩ := Finset.inf_mem_of_nonempty
      (f := candidate G weight old v) (show (Finset.univ : Finset (Fin n)).Nonempty from ⟨target, Finset.mem_univ _⟩)
    have chosen_value := chosen.trans value
    by_cases adjacent : G.Adj v u
    · simp only [candidate, if_pos adjacent] at chosen_value
      by_cases unreachable : old[u.val] = ⊤
      · simp [unreachable] at chosen_value
      · obtain ⟨r, finite⟩ := WithTop.ne_top_iff_exists.mp unreachable
        obtain ⟨walk, walk_cost⟩ := sound u r finite.symm
        rw [← finite, ← WithTop.coe_add, WithTop.coe_inj] at chosen_value
        exact ⟨.cons adjacent walk, by simpa only [traversalCost_cons, walk_cost] using chosen_value⟩
    · simp [candidate, adjacent] at chosen_value

theorem iterate_sound (target : Fin n) (rounds : ℕ) :
    Sound G weight target (iterate G weight target rounds) := by
  induction rounds with
  | zero => exact initial_sound G weight target
  | succ k ih => exact step_sound G weight target _ ih

theorem iterate_le_walk (target : Fin n) (rounds : ℕ) {v : Fin n}
    (walk : G.Walk v target) (length_bound : walk.length ≤ rounds) :
    (iterate G weight target rounds)[v.val] ≤ (traversalCost G weight walk : WithTop ℚ) := by
  induction rounds generalizing v with
  | zero =>
    cases walk with
    | nil => simp
    | cons edge tail => simp at length_bound
  | succ k ih =>
    cases walk with
    | nil => exact (step_le_old G weight _ target).trans (ih .nil (by simp))
    | @cons v u t edge tail =>
      have tail_bound : tail.length ≤ k := by simpa using length_bound
      calc
        _ ≤ (weight v : WithTop ℚ) + (iterate G weight target k)[u.val] := step_le_edge G weight _ edge
        _ ≤ (weight v : WithTop ℚ) + (traversalCost G weight tail : WithTop ℚ) :=
          add_le_add le_rfl (ih tail tail_bound)
        _ = _ := (WithTop.coe_add _ _).symm

theorem shortestDistances_eq_distance (nonneg : ∀ v, 0 ≤ weight v) (source target : Fin n)
    (reachable : Nonempty (G.Path source target)) :
    (shortestDistances G weight target)[source.val] =
      (NodeMetric.distance G weight source target reachable : WithTop ℚ) := by
  obtain ⟨path, path_cost⟩ := NodeMetric.exists_shortest G weight reachable
  have edge_bound : path.val.length ≤ n := by
    have bound := path.property.length_lt
    simpa only [Fintype.card_fin] using Nat.le_of_lt bound
  have upper := iterate_le_walk G weight target n path.val edge_bound
  rw [traversalCost_eq_supportWeight G weight path.val path.property, path_cost] at upper
  have finite : (iterate G weight target n)[source.val] ≠ ⊤ := by
    intro top
    rw [top] at upper
    simpa using upper
  obtain ⟨q, value⟩ := WithTop.ne_top_iff_exists.mp finite
  obtain ⟨walk, walk_cost⟩ := iterate_sound G weight target n source q value.symm
  have lower : NodeMetric.distance G weight source target reachable ≤ q := calc
    _ ≤ NodeMetric.walkWeight G weight walk.toPath.val := NodeMetric.distance_le_path G weight reachable _
    _ ≤ traversalCost G weight walk := erasedPath_cost_le G weight nonneg walk
    _ = q := walk_cost
  apply le_antisymm upper
  simpa only [shortestDistances, ← value, WithTop.coe_le_coe] using lower

theorem shortestDistances_eq_top_iff (nonneg : ∀ v, 0 ≤ weight v) (source target : Fin n) :
    (shortestDistances G weight target)[source.val] = ⊤ ↔ ¬ Nonempty (G.Path source target) := by
  constructor
  · intro value reachable
    rw [shortestDistances_eq_distance G weight nonneg source target reachable] at value
    simp at value
  · intro disconnected
    by_contra finite
    obtain ⟨q, value⟩ := WithTop.ne_top_iff_exists.mp finite
    obtain ⟨walk, _⟩ := iterate_sound G weight target n source q value.symm
    exact disconnected ⟨walk.toPath⟩

end BuyAtBulk.Computation.ShortestPath
