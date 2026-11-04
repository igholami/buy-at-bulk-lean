import BuyAtBulk.Statements.ZeroBuying
import BuyAtBulk.UpperBound.CoreFactors

/-! Empty request families and zero buying budgets in the full parameterized
rounding statement. Both budgets are preserved without division by zero. -/
noncomputable section
namespace BuyAtBulk.Statements

theorem empty_parameterized (I : Instance) (f : I.FractionalSolution)
    (hf : I.Feasible f) (empty : I.requestCount = 0) (ratio r : ℕ) :
    ParameterizedRoundedOutput I f ratio r 500000 := by
  classical
  letI : IsEmpty (Fin I.requestCount) := ⟨fun i => by have := i.isLt; omega⟩
  let routing : I.IntegralRouting := {
    path := fun i => isEmptyElim i
    allowed_path := fun i => isEmptyElim i }
  refine ⟨routing, ?_, ?_⟩
  · have factor_nonneg : 0 ≤ buyingFactor I.requestCount ratio r := by
      unfold buyingFactor
      positivity
    have budget_nonneg : (0 : ℝ) ≤ I.buyingCost f := by
      exact_mod_cast (Finset.sum_nonneg fun a _ => mul_nonneg (I.buying_nonneg a) (hf.1 a).1 :
        (0 : ℚ) ≤ I.buyingCost f)
    have zero : I.integralBuyingCost routing = 0 := by
      simp [Instance.integralBuyingCost, Instance.usedResources]
    rw [zero, Rat.cast_zero]
    positivity
  · simp [Instance.integralRentalCost, Instance.rentalCost]

theorem zero_buying_parameterized (I : Instance) (f : I.FractionalSolution)
    (hf : I.Feasible f) (zero : I.buyingCost f = 0) (hh : 0 < I.requestCount)
    (ratio r : ℕ) (hratio : 8 ≤ ratio) (hr : 1 ≤ r) :
    ParameterizedRoundedOutput I f ratio r 500000 := by
  obtain ⟨routing, buying, rental⟩ := I.zero_buying_rounding f hf zero
  have levels : (1 : ℝ) ≤ gridLevels I.requestCount ratio := by
    rw [← UpperBound.gridDepth_eq_gridLevels]
    exact_mod_cast UpperBound.gridDepth_pos I.requestCount ratio hh (by omega)
  have parameter : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have coefficient : 1 ≤ (500000 : ℝ) * ((r : ℝ) * gridLevels I.requestCount ratio) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr parameter) (sub_nonneg.mpr levels)]
  have budget_nonneg : (0 : ℝ) ≤ I.rentalCost f := by
    exact_mod_cast (Finset.sum_nonneg fun i _ => mul_nonneg (I.demand_pos i).le
      (Finset.sum_nonneg fun p _ => mul_nonneg
        (Finset.sum_nonneg fun a _ => I.length_nonneg a) (hf.2.1 i p)) :
      (0 : ℚ) ≤ I.rentalCost f)
  refine ⟨routing, by simp [buying, zero], ?_⟩
  calc
    (I.integralRentalCost routing : ℝ) ≤ I.rentalCost f := by exact_mod_cast rental
    _ = 1 * (I.rentalCost f : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right coefficient budget_nonneg

end BuyAtBulk.Statements
