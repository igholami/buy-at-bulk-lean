import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Resource/path incidence model of Definition 2.1. A graph realization and the
node subdivision reduction are separate obligations; this model does not assert them. -/
namespace BuyAtBulk

structure Instance where
  resourceCount : ℕ
  requestCount : ℕ
  pathCount : ℕ
  allowed : Fin requestCount → Fin pathCount → Bool
  uses : Fin pathCount → Finset (Fin resourceCount)
  buying : Fin resourceCount → ℚ
  length : Fin resourceCount → ℚ
  demand : Fin requestCount → ℚ
  buying_nonneg : ∀ a, 0 ≤ buying a
  length_nonneg : ∀ a, 0 ≤ length a
  demand_pos : ∀ i, 0 < demand i

namespace Instance

variable (I : Instance)

structure FractionalSolution where
  opening : Fin I.resourceCount → ℚ
  flow : Fin I.requestCount → Fin I.pathCount → ℚ

def pathLength (p : Fin I.pathCount) : ℚ := ∑ a ∈ I.uses p, I.length a

def resourceFlow (f : I.FractionalSolution) (i : Fin I.requestCount)
    (a : Fin I.resourceCount) : ℚ :=
  ∑ p : Fin I.pathCount, if a ∈ I.uses p then f.flow i p else 0

def Feasible (f : I.FractionalSolution) : Prop :=
  (∀ a, 0 ≤ f.opening a ∧ f.opening a ≤ 1) ∧
  (∀ i p, 0 ≤ f.flow i p) ∧
  (∀ i p, I.allowed i p = false → f.flow i p = 0) ∧
  (∀ i, ∑ p, f.flow i p = 1) ∧
  (∀ i a, I.resourceFlow f i a ≤ f.opening a)

def buyingCost (f : I.FractionalSolution) : ℚ := ∑ a, I.buying a * f.opening a

def fractionalLength (f : I.FractionalSolution) (i : Fin I.requestCount) : ℚ :=
  ∑ p, I.pathLength p * f.flow i p

def rentalCost (f : I.FractionalSolution) : ℚ :=
  ∑ i, I.demand i * I.fractionalLength f i

structure IntegralRouting where
  path : Fin I.requestCount → Fin I.pathCount
  allowed_path : ∀ i, I.allowed (i) (path i) = true

def usedResources (routing : I.IntegralRouting) : Finset (Fin I.resourceCount) :=
  Finset.univ.biUnion fun i => I.uses (routing.path i)

def integralBuyingCost (routing : I.IntegralRouting) : ℚ :=
  ∑ a ∈ I.usedResources routing, I.buying a

def integralRentalCost (routing : I.IntegralRouting) : ℚ :=
  ∑ i, I.demand i * I.pathLength (routing.path i)

end Instance
end BuyAtBulk
