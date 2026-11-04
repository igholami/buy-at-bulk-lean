import BuyAtBulk.Computation.ShortestPath.Recovery
import BuyAtBulk.Computation.ShortestPath.Complexity

/-! Conservative scheduled-operation accounting for executable recovery.
Each predecessor search is charged its full n-entry scan, even when `find?`
stops early. Recomputed Bellman–Ford tables are charged by their proved exact
relaxation count. A unit also pays the comparison deciding whether to stay. -/
namespace BuyAtBulk.Computation.ShortestPath

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (weight : Fin n → ℚ)

def recoverScheduled (target : Fin n) : (rounds : ℕ) → (v : Fin n) → Option (G.Walk v target) × ℕ
  | 0, v => (recover G weight target 0 v, 0)
  | rounds + 1, v =>
    let previous := iterate G weight target rounds
    let next := step G weight previous
    let paid := rounds * n * n + n * n + 1
    if previous[v.val] = next[v.val] then
      let recursive := recoverScheduled target rounds v
      (recursive.1, paid + recursive.2)
    else
      match found : edgeChoice G weight previous v next[v.val] with
      | none => (none, paid + n)
      | some u =>
        let recursive := recoverScheduled target rounds u
        (recursive.1.map (fun walk => .cons
          (edgeChoice_spec G weight previous v u next[v.val] found).1 walk), paid + n + recursive.2)

theorem recoverScheduled_value (target : Fin n) (rounds : ℕ) (v : Fin n) :
    (recoverScheduled G weight target rounds v).1 = recover G weight target rounds v := by
  induction rounds generalizing v with
  | zero => rfl
  | succ k ih =>
    simp only [recoverScheduled]
    rw [recover]
    split
    · exact ih v
    · split
      · rename_i missing
        split
        · rfl
        · rename_i u found
          rw [missing] at found
          contradiction
      · rename_i u found
        split
        · rename_i missing
          rw [found] at missing
          contradiction
        · rename_i u' found'
          have same : u' = u := Option.some.inj (found'.symm.trans found)
          subst u'
          rw [ih]

theorem recoverScheduled_bound (target : Fin n) (rounds : ℕ) (v : Fin n) :
    (recoverScheduled G weight target rounds v).2 ≤ rounds ^ 2 * n ^ 2 + rounds * n + rounds := by
  induction rounds generalizing v with
  | zero => simp [recoverScheduled]
  | succ k ih =>
    have stepBudget : k * n * n + n * n + 1 + n + (k ^ 2 * n ^ 2 + k * n + k) ≤
        (k + 1) ^ 2 * n ^ 2 + (k + 1) * n + (k + 1) := by
      nlinarith only [Nat.zero_le (k * n ^ 2)]
    simp only [recoverScheduled]
    split
    · have bound := ih v
      dsimp only
      exact (Nat.add_le_add_left bound _).trans (by omega)
    · split
      · dsimp only
        exact (Nat.le_add_right _ _).trans stepBudget
      · rename_i u found
        have bound := ih u
        dsimp only
        exact (Nat.add_le_add_left bound _).trans stepBudget

/-- Including recovery (which recomputes distance tables), the scheduled
candidate-evaluation and recovery-branch comparison budget is n⁴+n²+n.
This counter excludes the constant-per-row minimum overhead in distance-table
folds; it is not a complete primitive-operation or bit-time count. Cycle
erasure uses no weights. -/
theorem shortestPath_scheduled_bound (source target : Fin n) :
    (recoverScheduled G weight target n source).1.map (fun walk => walk.toPath) =
      shortestPath G weight source target ∧
    (recoverScheduled G weight target n source).2 ≤ n ^ 4 + n ^ 2 + n := by
  constructor
  · rw [recoverScheduled_value]
    rfl
  · have bound := recoverScheduled_bound G weight target n source
    convert bound using 1 <;> ring

end BuyAtBulk.Computation.ShortestPath
