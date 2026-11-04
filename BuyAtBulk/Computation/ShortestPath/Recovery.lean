import BuyAtBulk.Computation.ShortestPath.Correctness
import Mathlib.Data.List.FinRange

/-! Executable predecessor recovery decreases the Bellman–Ford round bound,
so zero-weight edges cannot cause cycling. It scans vertices, not paths.
The returned walk is erased constructively to an actual shortest simple path. -/
namespace BuyAtBulk.Computation.ShortestPath

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (weight : Fin n → ℚ)

def edgeChoice (old : Vector (WithTop ℚ) n) (v : Fin n) (value : WithTop ℚ) : Option (Fin n) :=
  (List.finRange n).find? fun u => decide (G.Adj v u ∧ (weight v : WithTop ℚ) + old[u.val] = value)

theorem edgeChoice_spec (old : Vector (WithTop ℚ) n) (v u : Fin n) (value : WithTop ℚ)
    (chosen : edgeChoice G weight old v value = some u) :
    G.Adj v u ∧ (weight v : WithTop ℚ) + old[u.val] = value := by
  unfold edgeChoice at chosen
  have property := List.find?_some chosen
  exact of_decide_eq_true property

theorem edgeChoice_exists (target : Fin n) (old : Vector (WithTop ℚ) n) (v : Fin n)
    (finite : (step G weight old)[v.val] ≠ ⊤)
    (not_stay : old[v.val] ≠ (step G weight old)[v.val]) :
    ∃ u, edgeChoice G weight old v (step G weight old)[v.val] = some u := by
  have not_le : ¬old[v.val] ≤ Finset.univ.inf (candidate G weight old v) := by
    intro le
    apply not_stay
    rw [step_get, min_eq_left le]
  have next_eq : (step G weight old)[v.val] = Finset.univ.inf (candidate G weight old v) := by
    rw [step_get, min_eq_right (le_of_not_ge not_le)]
  obtain ⟨u, _, chosen⟩ := Finset.inf_mem_of_nonempty
    (f := candidate G weight old v) (show (Finset.univ : Finset (Fin n)).Nonempty from ⟨target, Finset.mem_univ _⟩)
  have value : candidate G weight old v u = (step G weight old)[v.val] := chosen.trans next_eq.symm
  have adjacent : G.Adj v u := by
    by_contra missing
    simp only [candidate, if_neg missing] at value
    exact finite value.symm
  have pred : G.Adj v u ∧ (weight v : WithTop ℚ) + old[u.val] = (step G weight old)[v.val] :=
    ⟨adjacent, by simpa only [candidate, if_pos adjacent] using value⟩
  cases found : edgeChoice G weight old v (step G weight old)[v.val] with
  | some u => exact ⟨u, rfl⟩
  | none =>
    have impossible := (List.find?_eq_none.mp found) u (by simp)
    exact False.elim (impossible (by simpa using pred))

def recover (target : Fin n) : (rounds : ℕ) → (v : Fin n) → Option (G.Walk v target)
  | 0, v => if same : v = target then some ((SimpleGraph.Walk.nil : G.Walk v v).copy rfl same) else none
  | rounds + 1, v =>
    let old := iterate G weight target rounds
    let next := step G weight old
    if old[v.val] = next[v.val] then recover target rounds v else
      match found : edgeChoice G weight old v next[v.val] with
      | none => none
      | some u => (recover target rounds u).map fun walk =>
          .cons (edgeChoice_spec G weight old v u next[v.val] found).1 walk

theorem recover_valid (target : Fin n) (rounds : ℕ) (v : Fin n) (walk : G.Walk v target)
    (returned : recover G weight target rounds v = some walk) :
    (traversalCost G weight walk : WithTop ℚ) = (iterate G weight target rounds)[v.val] ∧
      walk.length ≤ rounds := by
  induction rounds generalizing v with
  | zero =>
    simp only [recover] at returned
    split at returned
    · rename_i same
      subst v
      simp only [SimpleGraph.Walk.copy_rfl_rfl, Option.some.injEq] at returned
      subst walk
      simp
    · contradiction
  | succ k ih =>
    rw [recover] at returned
    by_cases stay : (iterate G weight target k)[v.val] = (step G weight (iterate G weight target k))[v.val]
    · rw [if_pos stay] at returned
      obtain ⟨cost, length⟩ := ih v walk returned
      exact ⟨cost.trans stay, by omega⟩
    · rw [if_neg stay] at returned
      split at returned
      · contradiction
      · rename_i u found
        obtain ⟨tail, tail_returned, joined⟩ := Option.map_eq_some_iff.mp returned
        obtain ⟨cost, length⟩ := ih u tail tail_returned
        subst walk
        constructor
        · rw [traversalCost_cons, WithTop.coe_add, cost]
          exact (edgeChoice_spec G weight _ v u _ found).2
        · simp only [SimpleGraph.Walk.length_cons]
          omega

theorem recover_exists (target : Fin n) (rounds : ℕ) (v : Fin n)
    (finite : (iterate G weight target rounds)[v.val] ≠ ⊤) :
    ∃ walk, recover G weight target rounds v = some walk := by
  induction rounds generalizing v with
  | zero =>
    by_cases same : v = target
    · subst v
      exact ⟨.nil, by simp [recover]⟩
    · simp [same] at finite
  | succ k ih =>
    by_cases stay : (iterate G weight target k)[v.val] = (step G weight (iterate G weight target k))[v.val]
    · have old_finite : (iterate G weight target k)[v.val] ≠ ⊤ := by
        rw [stay]
        exact finite
      obtain ⟨walk, returned⟩ := ih v old_finite
      exact ⟨walk, by simpa only [recover, if_pos stay] using returned⟩
    · obtain ⟨u, found⟩ := edgeChoice_exists G weight target _ v finite stay
      have edge := edgeChoice_spec G weight _ v u _ found
      have old_finite : (iterate G weight target k)[u.val] ≠ ⊤ := by
        intro top
        apply finite
        change (step G weight (iterate G weight target k))[v.val] = ⊤
        rw [← edge.2, top]
        simp
      obtain ⟨walk, returned⟩ := ih u old_finite
      refine ⟨.cons edge.1 walk, ?_⟩
      rw [recover, if_neg stay]
      split
      · rename_i missing
        rw [found] at missing
        contradiction
      · rename_i u' found'
        have same : u' = u := Option.some.inj (found'.symm.trans found)
        subst u'
        simp only [returned, Option.map_some]

def shortestPath (source target : Fin n) : Option (G.Path source target) :=
  (recover G weight target n source).map fun walk => walk.toPath

theorem shortestPath_correct (nonneg : ∀ v, 0 ≤ weight v) (source target : Fin n)
    (reachable : Nonempty (G.Path source target)) :
    ∃ path, shortestPath G weight source target = some path ∧
      NodeMetric.walkWeight G weight path.val = NodeMetric.distance G weight source target reachable := by
  have result := shortestDistances_eq_distance G weight nonneg source target reachable
  have finite : (iterate G weight target n)[source.val] ≠ ⊤ := by
    change (shortestDistances G weight target)[source.val] ≠ ⊤
    rw [result]
    exact WithTop.coe_ne_top
  obtain ⟨walk, returned⟩ := recover_exists G weight target n source finite
  obtain ⟨cost, _⟩ := recover_valid G weight target n source walk returned
  have traversal_eq : traversalCost G weight walk = NodeMetric.distance G weight source target reachable := by
    apply WithTop.coe_injective
    exact cost.trans result
  refine ⟨walk.toPath, by simp only [shortestPath, returned, Option.map_some], ?_⟩
  apply le_antisymm
  · exact (erasedPath_cost_le G weight nonneg walk).trans_eq traversal_eq
  · exact NodeMetric.distance_le_path G weight reachable _

end BuyAtBulk.Computation.ShortestPath
