import BuyAtBulk.Model.FlowDecomposition
import Mathlib.Basic.Real.Basic

namespace BuyAtBulk.Instance

/-- Total number of positive commodity/path entries in an explicit path flow. -/
def positivePathCount (I : Instance) (f : I.FractionalSolution) : ℕ :=
  ∑ i, (Finset.univ.filter fun p => f.flow i p ≠ 0).card

/-- Rentals are a linear function of the per-commodity resource marginals. -/
theorem fractionalLength_eq_resource_sum (I : Instance) (f : I.FractionalSolution)
    (i : Fin I.requestCount) :
    I.fractionalLength f i = ∑ a, I.length a * I.resourceFlow f i a := by
  classical
  simp only [fractionalLength, pathLength, resourceFlow, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  simp

/-- Every feasible rational path LP has a feasible rational sparse replacement.
Openings and every resource marginal are unchanged; no new positive path appears.
The bound counts commodity/path pairs, so it also bounds distinct used paths. -/
theorem sparse_flow_decomposition (I : Instance) (f : I.FractionalSolution)
    (hf : I.Feasible f) :
    ∃ g : I.FractionalSolution, I.Feasible g ∧ g.opening = f.opening ∧
      (∀ i a, I.resourceFlow g i a = I.resourceFlow f i a) ∧
      (∀ i p, g.flow i p ≠ 0 → f.flow i p ≠ 0) ∧
      I.positivePathCount g ≤ I.requestCount * (I.resourceCount + 1) ∧
      I.buyingCost g = I.buyingCost f ∧ I.rentalCost g = I.rentalCost f := by
  classical
  let v : Fin I.pathCount → Fin I.resourceCount → ℚ :=
    fun p a => if a ∈ I.uses p then 1 else 0
  have each := fun i => FlowDecomposition.sparse_weights I.resourceCount v (f.flow i)
    (hf.2.1 i) (hf.2.2.2.1 i)
  choose z hz0 hzsum hzsupport hzcard hzv using each
  let g : I.FractionalSolution := ⟨f.opening, z⟩
  have marg : ∀ i a, I.resourceFlow g i a = I.resourceFlow f i a := by
    intro i a
    have h := congrFun (hzv i) a
    simpa [resourceFlow, g, v, Pi.smul_apply, Finset.sum_apply] using h
  refine ⟨g, ?_, rfl, marg, hzsupport, ?_, rfl, ?_⟩
  · refine ⟨hf.1, hz0, ?_, hzsum, ?_⟩
    · intro i p hip
      by_contra hnonzero
      exact hzsupport i p hnonzero (hf.2.2.1 i p hip)
    · intro i a; rw [marg]; exact hf.2.2.2.2 i a
  · calc
      I.positivePathCount g ≤ ∑ _i : Fin I.requestCount, (I.resourceCount + 1) :=
        Finset.sum_le_sum fun i _ => hzcard i
      _ = I.requestCount * (I.resourceCount + 1) := by simp
  · apply Finset.sum_congr rfl
    intro i _
    rw [fractionalLength_eq_resource_sum, fractionalLength_eq_resource_sum]
    simp_rw [marg]

/-- A budget-based rounder may consume the sparse LP without changing its input
budgets. This is the mathematical decomposition step, not a running-time claim. -/
theorem rounding_of_sparse_decomposition (I : Instance) (f : I.FractionalSolution)
    (hf : I.Feasible f) (A C : ℝ)
    (round : ∀ g : I.FractionalSolution, I.Feasible g →
      I.positivePathCount g ≤ I.requestCount * (I.resourceCount + 1) →
      ∃ routing : I.IntegralRouting,
        (I.integralBuyingCost routing : ℝ) ≤ A * I.buyingCost g ∧
        (I.integralRentalCost routing : ℝ) ≤ C * I.rentalCost g) :
    ∃ routing : I.IntegralRouting,
      (I.integralBuyingCost routing : ℝ) ≤ A * I.buyingCost f ∧
      (I.integralRentalCost routing : ℝ) ≤ C * I.rentalCost f := by
  obtain ⟨g, hg, _, _, _, hsize, hB, hR⟩ := I.sparse_flow_decomposition f hf
  obtain ⟨routing, hb, hr⟩ := round g hg hsize
  exact ⟨routing, by simpa [hB] using hb, by simpa [hR] using hr⟩

end BuyAtBulk.Instance
