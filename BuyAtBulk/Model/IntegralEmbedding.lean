import BuyAtBulk.Model.NaturalLP
import Mathlib.Tactic.NormNum

/-! Every integral routing gives a feasible natural affine LP solution with the
same separate budgets. This is the relaxation step used by Theorem 1. -/
namespace BuyAtBulk.Instance

variable (I : BuyAtBulk.Instance)

def toFractional (routing : I.IntegralRouting) : I.FractionalSolution where
  opening a := if a ∈ I.usedResources routing then 1 else 0
  flow i p := if p = routing.path i then 1 else 0

@[simp] theorem toFractional_resourceFlow (routing : I.IntegralRouting)
    (i : Fin I.requestCount) (a : Fin I.resourceCount) :
    I.resourceFlow (I.toFractional routing) i a =
      if a ∈ I.uses (routing.path i) then 1 else 0 := by
  classical
  simp only [resourceFlow, toFractional]
  rw [Finset.sum_eq_single (routing.path i)]
  · simp
  · intro p _ hp
    simp [hp]
  · simp

theorem toFractional_feasible (routing : I.IntegralRouting) :
    I.Feasible (I.toFractional routing) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a
    simp only [toFractional]
    split_ifs <;> norm_num
  · intro i p
    simp only [toFractional]
    split_ifs <;> norm_num
  · intro i p hp
    have hne : p ≠ routing.path i := by
      intro heq
      subst p
      have ht := routing.allowed_path i
      simp [ht] at hp
    simp [toFractional, hne]
  · intro i
    simp only [toFractional]
    rw [Finset.sum_eq_single (routing.path i)]
    · simp
    · intro p _ hp
      simp [hp]
    · simp
  · intro i a
    rw [I.toFractional_resourceFlow]
    by_cases ha : a ∈ I.uses (routing.path i)
    · have hu : a ∈ I.usedResources routing := by
        simp only [usedResources, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, ha⟩
      simp [ha, toFractional, hu]
    · simp only [ha, ↓reduceIte, toFractional]
      split_ifs <;> norm_num

theorem toFractional_buyingCost (routing : I.IntegralRouting) :
    I.buyingCost (I.toFractional routing) = I.integralBuyingCost routing := by
  classical
  simp only [buyingCost, toFractional, integralBuyingCost]
  simp

theorem toFractional_rentalCost (routing : I.IntegralRouting) :
    I.rentalCost (I.toFractional routing) = I.integralRentalCost routing := by
  classical
  simp only [rentalCost, fractionalLength, toFractional, integralRentalCost]
  congr 1
  funext i
  congr 1
  rw [Finset.sum_eq_single (routing.path i)]
  · simp
  · intro p _ hp
    simp [hp]
  · simp

end BuyAtBulk.Instance
