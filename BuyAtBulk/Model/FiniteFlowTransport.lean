import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Rat.BigOperators

/-! Finite flow pushforward on typed path spaces, summing fibers exactly. -/
noncomputable section
namespace BuyAtBulk.FiniteFlow

variable {P Q : Type} [Fintype P] [Fintype Q]
local instance finiteFlowTransportLocalInst1 : DecidableEq Q := Classical.decEq Q

def push (map : P → Q) (flow : P → ℚ) (q : Q) : ℚ :=
  ∑ p, if map p = q then flow p else 0

theorem weighted_push (map : P → Q) (flow : P → ℚ) (weight : Q → ℚ) :
    (∑ q, weight q * push map flow q) = ∑ p, weight (map p) * flow p := by
  unfold push
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  simp

end BuyAtBulk.FiniteFlow
