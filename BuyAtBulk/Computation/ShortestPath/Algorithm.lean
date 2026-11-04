import BuyAtBulk.Computation.ShortestPath.Traversal
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Data.Vector.Basic

/-! Executable dense Bellman–Ford on indexed finite vertices. Each previous
round is materialized as an array-backed vector before any next-round lookups;
no simple-path enumeration occurs in the algorithm. `⊤` means unreachable. -/
namespace BuyAtBulk.Computation.ShortestPath

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (weight : Fin n → ℚ)

def initial (target : Fin n) : Vector (WithTop ℚ) n :=
  Vector.ofFn fun v => if v = target then (weight target : WithTop ℚ) else ⊤

def candidate (old : Vector (WithTop ℚ) n) (v u : Fin n) : WithTop ℚ :=
  if G.Adj v u then (weight v : WithTop ℚ) + old[u.val] else ⊤

def step (old : Vector (WithTop ℚ) n) : Vector (WithTop ℚ) n :=
  Vector.ofFn fun v => min old[v.val] (Finset.univ.inf fun u => candidate G weight old v u)

def iterate (target : Fin n) : ℕ → Vector (WithTop ℚ) n
  | 0 => initial weight target
  | rounds + 1 => let previous := iterate target rounds; step G weight previous

def shortestDistances (target : Fin n) : Vector (WithTop ℚ) n := iterate G weight target n

@[simp] theorem initial_get (target v : Fin n) :
    (initial weight target)[v.val] = if v = target then (weight target : WithTop ℚ) else ⊤ := by
  simp [initial]

@[simp] theorem step_get (old : Vector (WithTop ℚ) n) (v : Fin n) :
    (step G weight old)[v.val] = min old[v.val] (Finset.univ.inf fun u => candidate G weight old v u) := by
  simp [step]

@[simp] theorem iterate_zero (target : Fin n) : iterate G weight target 0 = initial weight target := rfl
@[simp] theorem iterate_succ (target : Fin n) (k : ℕ) :
    iterate G weight target (k + 1) = step G weight (iterate G weight target k) := rfl

theorem step_le_old (old : Vector (WithTop ℚ) n) (v : Fin n) :
    (step G weight old)[v.val] ≤ old[v.val] := by rw [step_get]; exact min_le_left _ _

theorem step_le_edge (old : Vector (WithTop ℚ) n) {v u : Fin n} (adjacent : G.Adj v u) :
    (step G weight old)[v.val] ≤ (weight v : WithTop ℚ) + old[u.val] := by
  rw [step_get]
  exact (min_le_right _ _).trans ((Finset.inf_le (Finset.mem_univ u)).trans_eq (if_pos adjacent))

end BuyAtBulk.Computation.ShortestPath
