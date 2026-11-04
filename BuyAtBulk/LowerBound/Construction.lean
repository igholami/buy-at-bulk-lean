import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic

/-! The set-cover core of `lower_bound.tex`, `thm:node-lower`.
The graph-realization and arbitrary-request padding are separate obligations. -/
namespace BuyAtBulk.LowerBound
open scoped BigOperators

/-- Paid nodes are the `2k` ground elements. -/
abbrev Ground (k : ℕ) := Fin (2 * k)

/-- A bought set must meet every request, which is a `k`-subset. -/
def HitsAll (k : ℕ) (C : Finset (Ground k)) : Prop :=
  ∀ A : Finset (Ground k), A.card = k → ∃ j ∈ A, j ∈ C

/-- Necessary covering constraints for any feasible network path LP.
Their sufficiency for the paper graph remains to be formalized using two-edge paths. -/
def FractionalCover (k : ℕ) (x : Ground k → ℝ) : Prop :=
  (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧
  ∀ A : Finset (Ground k), A.card = k → 1 ≤ ∑ j ∈ A, x j

end BuyAtBulk.LowerBound
