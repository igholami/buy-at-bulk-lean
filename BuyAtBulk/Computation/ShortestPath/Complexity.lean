import BuyAtBulk.Computation.ShortestPath.Algorithm
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring

/-! An instrumented implementation counts every candidate relaxation, including
nonedges (whose cost is at most that of an edge). Its computed distance vector
is proved equal to the uninstrumented recurrence. The bound counts rational
arithmetic/comparison operations, not rational bit complexity. -/
namespace BuyAtBulk.Computation.ShortestPath

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (weight : Fin n → ℚ)

def countedScan (old : Vector (WithTop ℚ) n) (v : Fin n) : List (Fin n) → WithTop ℚ × ℕ
  | [] => (old[v.val], 0)
  | u :: rest =>
    let result := countedScan old v rest
    (min (candidate G weight old v u) result.1, result.2 + 1)

theorem countedScan_value (old : Vector (WithTop ℚ) n) (v : Fin n) (vertices : List (Fin n)) :
    (countedScan G weight old v vertices).1 =
      min old[v.val] (vertices.toFinset.inf fun u => candidate G weight old v u) := by
  induction vertices with
  | nil => simp [countedScan]
  | cons u rest ih =>
    simp only [countedScan, ih, List.toFinset_cons, Finset.inf_insert]
    change min _ (min _ _) = min _ (min _ _)
    exact min_left_comm _ _ _

@[simp] theorem countedScan_count (old : Vector (WithTop ℚ) n) (v : Fin n) (vertices : List (Fin n)) :
    (countedScan G weight old v vertices).2 = vertices.length := by
  induction vertices with
  | nil => rfl
  | cons u rest ih => simp only [countedScan, ih, List.length_cons]

def countedStep (old : Vector (WithTop ℚ) n) : Vector (WithTop ℚ) n × ℕ :=
  let rows := Vector.ofFn fun v => countedScan G weight old v (List.finRange n)
  (rows.map Prod.fst, ∑ v : Fin n, (rows[v.val]).2)

theorem countedStep_eq (old : Vector (WithTop ℚ) n) :
    countedStep G weight old = (step G weight old, n * n) := by
  apply Prod.ext
  · apply Vector.ext
    intro i hi
    simp only [countedStep, Vector.getElem_map, Vector.getElem_ofFn, step, countedScan_value]
    simp
  · simp [countedStep]

def countedIterate (target : Fin n) : ℕ → Vector (WithTop ℚ) n × ℕ
  | 0 => (initial weight target, 0)
  | rounds + 1 =>
    let previous := countedIterate target rounds
    let next := countedStep G weight previous.1
    (next.1, previous.2 + next.2)

theorem countedIterate_eq (target : Fin n) (rounds : ℕ) :
    countedIterate G weight target rounds = (iterate G weight target rounds, rounds * n * n) := by
  induction rounds with
  | zero => simp [countedIterate]
  | succ k ih =>
    simp only [countedIterate, ih, countedStep_eq, iterate_succ]
    congr 1
    ring

/-- At most one rational addition and one minimum comparison per scheduled
candidate. The materialized n-round implementation schedules exactly n³ of them. -/
theorem shortest_relaxation_count (target : Fin n) :
    (countedIterate G weight target n).1 = shortestDistances G weight target ∧
      (countedIterate G weight target n).2 = n ^ 3 := by
  rw [countedIterate_eq]
  constructor
  · rfl
  · ring

end BuyAtBulk.Computation.ShortestPath
