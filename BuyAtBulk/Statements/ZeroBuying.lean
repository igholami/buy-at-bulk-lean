import BuyAtBulk.Model.NaturalLP
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-! Full incidence-model form of `lem:zero-buying`: selecting a positive-flow
path no longer than its fractional average preserves zero buying exactly.
No shortest-path algorithm or polynomial-time implementation is asserted. -/
namespace BuyAtBulk.Instance

/-- A unit nonnegative finite path flow has a positive-flow path whose length
is at most the average physical length. -/
theorem exists_short_positive_path (I : BuyAtBulk.Instance)
    (f : I.FractionalSolution) (feasible : I.Feasible f) (i : Fin I.requestCount) :
    ∃ p, 0 < f.flow i p ∧ I.pathLength p ≤ I.fractionalLength f i := by
  classical
  have nonneg := feasible.2.1 i
  have unit := feasible.2.2.2.1 i
  have positive : ∃ p, 0 < f.flow i p := by
    by_contra hn
    push Not at hn
    have zero : ∀ p, f.flow i p = 0 := fun p => le_antisymm (hn p) (nonneg p)
    simp [zero] at unit
  by_contra hn
  push Not at hn
  have terms_nonneg : ∀ p, 0 ≤ (I.pathLength p - I.fractionalLength f i) * f.flow i p := by
    intro p
    by_cases hp : 0 < f.flow i p
    · exact mul_nonneg (sub_nonneg.mpr (hn p hp).le) (nonneg p)
    · have hz : f.flow i p = 0 := le_antisymm (le_of_not_gt hp) (nonneg p)
      simp [hz]
  obtain ⟨p, hp⟩ := positive
  have sum_positive : 0 < ∑ q, (I.pathLength q - I.fractionalLength f i) * f.flow i q := by
    apply Finset.sum_pos' (fun q _ => terms_nonneg q)
    exact ⟨p, Finset.mem_univ p, mul_pos (sub_pos.mpr (hn p hp)) hp⟩
  have sum_zero : (∑ q, (I.pathLength q - I.fractionalLength f i) * f.flow i q) = 0 := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, unit, mul_one]
    exact sub_self _
  linarith

/-- Every resource used by a positive LP path has zero buying price when
the fractional buying budget is zero. -/
theorem positive_path_zero_buying (I : BuyAtBulk.Instance)
    (f : I.FractionalSolution) (feasible : I.Feasible f) (zero_buying : I.buyingCost f = 0)
    (i : Fin I.requestCount) (p : Fin I.pathCount) (positive : 0 < f.flow i p)
    (a : Fin I.resourceCount) (used : a ∈ I.uses p) : I.buying a = 0 := by
  classical
  have term_nonneg : ∀ a, 0 ≤ I.buying a * f.opening a :=
    fun a => mul_nonneg (I.buying_nonneg a) (feasible.1 a).1
  have term_zero : I.buying a * f.opening a = 0 := by
    have hs : ∑ a, I.buying a * f.opening a = 0 := zero_buying
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => term_nonneg a)).mp hs a (Finset.mem_univ a)
  have flow_le : f.flow i p ≤ I.resourceFlow f i a := by
    unfold resourceFlow
    calc
      _ = (if a ∈ I.uses p then f.flow i p else 0) := by simp [used]
      _ ≤ ∑ q, if a ∈ I.uses q then f.flow i q else 0 := by
        apply Finset.single_le_sum (s := Finset.univ)
          (f := fun q : Fin I.pathCount => if a ∈ I.uses q then f.flow i q else 0)
        · intro q _
          split_ifs
          · exact feasible.2.1 i q
          · exact le_rfl
        · exact Finset.mem_univ p
  have opening_pos : 0 < f.opening a := lt_of_lt_of_le positive
    (flow_le.trans (feasible.2.2.2.2 i a))
  exact (mul_eq_zero.mp term_zero).resolve_right (ne_of_gt opening_pos)

/-- The zero-buying-budget rounding conclusion, including the exact rental
factor one, valid for any finite resource/path incidence instance. -/
theorem zero_buying_rounding (I : BuyAtBulk.Instance)
    (f : I.FractionalSolution) (feasible : I.Feasible f) (zero_buying : I.buyingCost f = 0) :
    ∃ routing : I.IntegralRouting,
      I.integralBuyingCost routing = 0 ∧ I.integralRentalCost routing ≤ I.rentalCost f := by
  classical
  let selected := fun i => Classical.choose (I.exists_short_positive_path f feasible i)
  have selected_spec : ∀ i, 0 < f.flow i (selected i) ∧
      I.pathLength (selected i) ≤ I.fractionalLength f i :=
    fun i => Classical.choose_spec (I.exists_short_positive_path f feasible i)
  have allowed : ∀ i, I.allowed i (selected i) = true := by
    intro i
    cases ha : I.allowed i (selected i) with
    | false =>
      have hz := feasible.2.2.1 i (selected i) ha
      exact False.elim ((ne_of_gt (selected_spec i).1) hz)
    | true => rfl
  let routing : I.IntegralRouting := ⟨selected, allowed⟩
  refine ⟨routing, ?_, ?_⟩
  · unfold integralBuyingCost
    apply Finset.sum_eq_zero
    intro a ha
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ha
    exact I.positive_path_zero_buying f feasible zero_buying i (selected i)
      (selected_spec i).1 a hi
  · unfold integralRentalCost rentalCost
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (selected_spec i).2 (I.demand_pos i).le

end BuyAtBulk.Instance
