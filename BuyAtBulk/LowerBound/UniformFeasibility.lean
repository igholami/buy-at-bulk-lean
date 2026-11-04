import BuyAtBulk.LowerBound.GraphLP

namespace BuyAtBulk.LowerBound
open scoped BigOperators

/-- Each paid node is used by at most one of the direct paths of a request. -/
theorem uniform_resourceFlow (k h : ℕ) (request : Fin h → Request k)
    (i : Fin h) (a : Ground k) :
    (graphData k h request).toInstance.resourceFlow (uniformSolution k h request) i a =
      if a ∈ (request i).val then 1 / (k : ℚ) else 0 := by
  classical
  let D := graphData k h request
  let code := fun j : (request i).val => D.encode i (shortPath k (request i) j)
  change (∑ p, if a ∈ D.toInstance.uses p then
    ∑ j : (request i).val, if code j = p then (1 / (k : ℚ)) else 0 else 0) = _
  calc
    _ = ∑ p, ∑ j : (request i).val,
        if code j = p then (if a ∈ D.toInstance.uses p then 1 / (k : ℚ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      by_cases ha : a ∈ D.toInstance.uses p
      · simp [ha]
      · simp [ha]
    _ = ∑ j : (request i).val, ∑ p,
        if code j = p then (if a ∈ D.toInstance.uses p then 1 / (k : ℚ) else 0) else 0 :=
      Finset.sum_comm
    _ = ∑ j : (request i).val,
        if a ∈ D.toInstance.uses (code j) then 1 / (k : ℚ) else 0 := by simp
    _ = ∑ j : (request i).val, if j.val = a then 1 / (k : ℚ) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hres : D.toInstance.uses (code j) = {j.val} :=
        (D.uses_encode i _).trans (shortPath_resources k h request i j)
      rw [hres]
      simp [eq_comm]
    _ = _ := by
      by_cases ha : a ∈ (request i).val
      · have heq : ∀ j : (request i).val, (j.val = a) ↔ j = ⟨a, ha⟩ := by
          intro j
          constructor
          · intro heq; exact Subtype.ext heq
          · intro heq; exact congrArg Subtype.val heq
        simp_rw [heq]
        simp [ha]
      · have hne : ∀ j : (request i).val, j.val ≠ a := by
          intro j heq
          apply ha
          exact heq ▸ j.property
        simp [hne, ha]

/-- The paper's fractional witness is feasible even after arbitrary request
repetition, because sharing is per commodity, with no aggregate capacity. -/
theorem uniform_feasible (k h : ℕ) (hk : 1 ≤ k) (request : Fin h → Request k) :
    (graphData k h request).toInstance.Feasible (uniformSolution k h request) := by
  classical
  let D := graphData k h request
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a
    change 0 ≤ 1 / (k : ℚ) ∧ 1 / (k : ℚ) ≤ 1
    exact ⟨by positivity, (div_le_one hkq).mpr (by exact_mod_cast hk)⟩
  · intro i p
    change 0 ≤ ∑ j : (request i).val,
      if D.encode i (shortPath k (request i) j) = p then 1 / (k : ℚ) else 0
    positivity
  · intro i p hp
    change (∑ j : (request i).val,
      if D.encode i (shortPath k (request i) j) = p then 1 / (k : ℚ) else 0) = 0
    apply Finset.sum_eq_zero
    intro j hj
    have hne : D.encode i (shortPath k (request i) j) ≠ p := by
      intro heq
      have := D.allowed_encode i (shortPath k (request i) j)
      rw [heq, hp] at this
      contradiction
    simp [hne]
  · intro i
    change (∑ p, ∑ j : (request i).val,
      if D.encode i (shortPath k (request i) j) = p then 1 / (k : ℚ) else 0) = 1
    rw [Finset.sum_comm]
    simp [(request i).property, ne_of_gt hkq]
  · intro i a
    rw [uniform_resourceFlow]
    change (if a ∈ (request i).val then 1 / (k : ℚ) else 0) ≤ 1 / (k : ℚ)
    split_ifs
    · exact le_rfl
    · positivity

/-- The same rational buying budget two works for every number of repeats. -/
theorem uniform_buyingCost (k h : ℕ) (hk : 1 ≤ k) (request : Fin h → Request k) :
    (graphData k h request).toInstance.buyingCost (uniformSolution k h request) = 2 := by
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  simp only [Instance.buyingCost, GraphData.toInstance, graphData, uniformSolution,
    one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [ne_of_gt hkq]

end BuyAtBulk.LowerBound
