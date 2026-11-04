import BuyAtBulk.Computation.PolynomialLP.ObjectivePrecision
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Exact objective faces retain the original vertices. This prevents repeated
coordinate fixing from introducing exponential encoding-bound recurrences. -/
noncomputable section
namespace BuyAtBulk.PolynomialLP
open RationalLP
open scoped BigOperators
variable {J C : Type} [Fintype J] [Fintype C]

theorem feasible_small_step (P : Problem J C) (x d : J → ℚ) (feasible : P.Feasible x)
    (vanishes : ∀ i ∈ P.active x, P.row i d = 0) :
    ∃ t : ℚ, 0 < t ∧ P.Feasible (x+t•d) := by
  classical
  let S : ℚ := 1+∑ i, |P.row i d|/(P.bound i-P.row i x)
  have terms : ∀ i : C, 0 ≤ |P.row i d|/(P.bound i-P.row i x) :=
    fun i => div_nonneg (abs_nonneg _) (sub_nonneg.mpr (feasible i))
  have Spos : 0 < S := by
    have nonnegative : 0 ≤ ∑ i : C, |P.row i d|/(P.bound i-P.row i x) :=
      Finset.sum_nonneg (fun i _ => terms i)
    dsimp [S]
    linarith
  let t : ℚ := 1/S
  have tpos : 0 < t := one_div_pos.mpr Spos
  have cancel : t*S = 1 := by dsimp [t]; field_simp
  refine ⟨t,tpos,?_⟩
  intro i
  simp only [map_add, map_smul, smul_eq_mul]
  by_cases active : i ∈ P.active x
  · rw [vanishes i active, mul_zero, add_zero]
    exact feasible i
  have slack : 0 < P.bound i-P.row i x := by
    have unequal : P.row i x ≠ P.bound i := by simpa [Problem.active] using active
    exact sub_pos.mpr (lt_of_le_of_ne (feasible i) unequal)
  have term := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset C)) => terms j) (Finset.mem_univ i)
  have rate : |P.row i d|/(P.bound i-P.row i x) ≤ S := by dsimp [S]; linarith
  have deriv : |P.row i d| ≤ S*(P.bound i-P.row i x) := (div_le_iff₀ slack).mp rate
  have bound : t*|P.row i d| ≤ P.bound i-P.row i x := by
    calc
      _ ≤ t*(S*(P.bound i-P.row i x)) := mul_le_mul_of_nonneg_left deriv tpos.le
      _ = _ := by rw [← mul_assoc,cancel,one_mul]
  have signed := mul_le_mul_of_nonneg_left (le_abs_self (P.row i d)) tpos.le
  linarith

theorem optimal_direction_flat (P : Problem J C) (x d : J → ℚ) (feasible : P.Feasible x)
    (minimal : ∀ y, P.Feasible y → P.objective x ≤ P.objective y)
    (vanishes : ∀ i ∈ P.active x, P.row i d = 0) : P.objective d = 0 := by
  obtain ⟨a,apos,af⟩ := feasible_small_step P x d feasible vanishes
  obtain ⟨b,bpos,bf⟩ := feasible_small_step P x (-d) feasible
    (by intro i member; simp [map_neg,vanishes i member])
  have forward := minimal _ af
  have backward := minimal _ bf
  simp only [map_add,map_smul,map_neg,smul_eq_mul] at forward backward
  nlinarith

def objectiveFace (P : Problem J C) (value : ℚ) : Problem J (C ⊕ Bool) where
  row
    | .inl i => P.row i
    | .inr upper => if upper then P.objective else -P.objective
  bound
    | .inl i => P.bound i
    | .inr upper => if upper then value else -value
  objective := P.objective

theorem objectiveFace_feasible (P : Problem J C) (value : ℚ) (x : J → ℚ) :
    (objectiveFace P value).Feasible x ↔ P.Feasible x ∧ P.objective x = value := by
  constructor
  · intro feasible
    have upper := feasible (.inr true)
    have lower := feasible (.inr false)
    simp only [objectiveFace, Bool.false_eq_true, ↓reduceIte, LinearMap.neg_apply] at upper lower
    exact ⟨fun i => feasible (.inl i),by linarith⟩
  · rintro ⟨feasible,equal⟩ c
    cases c with
    | inl i => exact feasible i
    | inr b => cases b <;> simp [objectiveFace,equal]

/-- A vertex of an attained minimum face is a vertex of the original LP,
with no objective coefficient restrictions. -/
theorem objectiveFace_vertex (P : Problem J C) (value : ℚ) (x : J → ℚ)
    (feasible : (objectiveFace P value).Feasible x)
    (minimal : ∀ y, P.Feasible y → P.objective x ≤ P.objective y)
    (vertex : (objectiveFace P value).Vertex x) : P.Vertex x := by
  classical
  obtain ⟨original_feasible,value_eq⟩ := (objectiveFace_feasible P value x).mp feasible
  intro y equalities
  have direction : ∀ i ∈ P.active x, P.row i (y-x) = 0 := by
    intro i member
    have active := (Finset.mem_filter.mp member).2
    simp only [map_sub,equalities i member,active,sub_self]
  have flat := optimal_direction_flat P x (y-x) original_feasible minimal direction
  have objective_y : P.objective y = value := by rw [map_sub] at flat; linarith
  apply vertex y
  intro c member
  cases c with
  | inl i =>
    apply equalities i
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    exact (Finset.mem_filter.mp member).2
  | inr b => cases b <;> simp [objectiveFace,objective_y]

end BuyAtBulk.PolynomialLP
