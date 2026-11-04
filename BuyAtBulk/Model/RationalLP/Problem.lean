import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Field.Basic

/-! Fixed-data finite rational linear programs. These definitions concern exact
mathematical optimization, separately from an executable or polynomial solver. -/
namespace BuyAtBulk.RationalLP

variable (J C : Type) [Fintype J] [Fintype C]

structure Problem where
  row : C → (J → ℚ) →ₗ[ℚ] ℚ
  bound : C → ℚ
  objective : (J → ℚ) →ₗ[ℚ] ℚ

namespace Problem
variable {J C} (P : Problem J C)

def Feasible (x : J → ℚ) : Prop := ∀ i, P.row i x ≤ P.bound i

noncomputable def active (x : J → ℚ) : Finset C := by
  classical
  exact Finset.univ.filter fun i => P.row i x = P.bound i

/-- The active equalities uniquely determine this rational point. -/
def Vertex (x : J → ℚ) : Prop :=
  ∀ y : J → ℚ, (∀ i ∈ P.active x, P.row i y = P.bound i) → y = x

/-- An explicit compactness hypothesis, stated as a rational unit-cube bound.
For compact graph-flow LPs this follows from node capacities and conservation. -/
def InUnitCube : Prop :=
  ∀ x, P.Feasible x → ∀ j, 0 ≤ x j ∧ x j ≤ 1

/-- Source mathematical target: an exact rational feasible minimizer. -/
def HasMinimum : Prop :=
  ∃ x, P.Feasible x ∧ ∀ y, P.Feasible y → P.objective x ≤ P.objective y

end Problem
end BuyAtBulk.RationalLP
