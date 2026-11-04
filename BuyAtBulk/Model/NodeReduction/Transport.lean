import BuyAtBulk.Model.NaturalLP
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace BuyAtBulk.NodeReduction
open scoped BigOperators

/-- Change only the complete path presentation, retaining all original
resources, prices, lengths, demands, and request indices. -/
abbrev repath (I : Instance) (pathCount : ℕ)
    (allowed : Fin I.requestCount → Fin pathCount → Bool)
    (uses : Fin pathCount → Finset (Fin I.resourceCount)) : Instance :=
  { I with pathCount := pathCount, allowed := allowed, uses := uses }

/-- Finite path flows push forward by summing fibers, without assuming a
bijection of fractional opening vectors or a path-map injectivity condition. -/
def pushflow {m n : ℕ} (map : Fin m → Fin n) (flow : Fin m → ℚ) (q : Fin n) : ℚ :=
  ∑ p, if map p = q then flow p else 0

theorem weighted_pushflow {m n : ℕ} (map : Fin m → Fin n) (flow : Fin m → ℚ)
    (weight : Fin n → ℚ) :
    ∑ q, weight q * pushflow map flow q = ∑ p, weight (map p) * flow p := by
  unfold pushflow
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  simp

section
variable (I : Instance) (n : ℕ)
    (allowed : Fin I.requestCount → Fin n → Bool)
    (uses : Fin n → Finset (Fin I.resourceCount))
    (map : Fin I.pathCount → Fin n)
    (hallowed : ∀ i p, allowed i (map p) = I.allowed i p)
    (huses : ∀ p, uses (map p) = I.uses p)

/-- The path-flow pushforward keeps every resource opening unchanged. -/
def transportFractional (f : I.FractionalSolution) : (repath I n allowed uses).FractionalSolution where
  opening := f.opening
  flow := fun i => pushflow map (f.flow i)

include huses in
theorem transport_resourceFlow (f : I.FractionalSolution) (i : Fin I.requestCount)
    (a : Fin I.resourceCount) :
    (repath I n allowed uses).resourceFlow (transportFractional I n allowed uses map f) i a =
      I.resourceFlow f i a := by
  have hw := weighted_pushflow map (f.flow i) (fun q => if a ∈ uses q then 1 else 0)
  simpa [Instance.resourceFlow, transportFractional, huses] using hw

include hallowed huses in
theorem transport_feasible (f : I.FractionalSolution) (hf : I.Feasible f) :
    (repath I n allowed uses).Feasible (transportFractional I n allowed uses map f) := by
  refine ⟨hf.1, ?_, ?_, ?_, ?_⟩
  · intro i q
    change 0 ≤ ∑ p, if map p = q then f.flow i p else 0
    apply Finset.sum_nonneg
    intro p hp
    split_ifs
    · exact hf.2.1 i p
    · exact le_rfl
  · intro i q hq
    change (∑ p, if map p = q then f.flow i p else 0) = 0
    apply Finset.sum_eq_zero
    intro p hp
    split_ifs with heq
    · apply hf.2.2.1 i p
      rw [← hallowed i p, heq]
      exact hq
    · rfl
  · intro i
    have hw := weighted_pushflow map (f.flow i) (fun _ => 1)
    simpa [transportFractional, hf.2.2.2.1 i] using hw
  · intro i a
    rw [transport_resourceFlow I n allowed uses map huses]
    exact hf.2.2.2.2 i a

theorem transport_buyingCost (f : I.FractionalSolution) :
    (repath I n allowed uses).buyingCost (transportFractional I n allowed uses map f) =
      I.buyingCost f := rfl

include huses in
theorem transport_rentalCost (f : I.FractionalSolution) :
    (repath I n allowed uses).rentalCost (transportFractional I n allowed uses map f) =
      I.rentalCost f := by
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  have hw := weighted_pushflow map (f.flow i) (fun q => (repath I n allowed uses).pathLength q)
  simpa [Instance.fractionalLength, Instance.pathLength, transportFractional, huses] using hw

/-- Integral routing transport uses the same path map. -/
def transportIntegral (routing : I.IntegralRouting) : (repath I n allowed uses).IntegralRouting where
  path := fun i => map (routing.path i)
  allowed_path := fun i => (hallowed i (routing.path i)).trans (routing.allowed_path i)

include huses in
theorem transport_usedResources (routing : I.IntegralRouting) :
    (repath I n allowed uses).usedResources (transportIntegral I n allowed uses map hallowed routing) =
      I.usedResources routing := by
  simp [Instance.usedResources, transportIntegral, huses]

include huses in
theorem transport_integralBuyingCost (routing : I.IntegralRouting) :
    (repath I n allowed uses).integralBuyingCost
      (transportIntegral I n allowed uses map hallowed routing) = I.integralBuyingCost routing := by
  unfold Instance.integralBuyingCost
  rw [transport_usedResources I n allowed uses map hallowed huses]

include huses in
theorem transport_integralRentalCost (routing : I.IntegralRouting) :
    (repath I n allowed uses).integralRentalCost
      (transportIntegral I n allowed uses map hallowed routing) = I.integralRentalCost routing := by
  simp [Instance.integralRentalCost, Instance.pathLength, transportIntegral, huses]

end
end BuyAtBulk.NodeReduction
