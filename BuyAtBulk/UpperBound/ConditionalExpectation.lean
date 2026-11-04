import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Explicit rational product estimator and sequential conditional expectation.
Each branch value is computed from sums/products, not by enumerating subsets. -/
namespace BuyAtBulk.ConditionalExpectation

variable {V R : Type} [Fintype R]

/-- The cost term plus the sum of product pessimistic estimators. Factors for
selected nodes are fixed; remaining nodes retain their independent probabilities. -/
def potential (buying probability : V → ℚ) (factor : R → V → ℚ)
    (amplitude : R → ℚ) (fixedCost normalization : ℚ) (selected remaining : List V) : ℚ :=
  (fixedCost + (selected.map buying).sum + (remaining.map fun v => probability v * buying v).sum) /
      normalization +
    ∑ r, amplitude r * (selected.map (factor r)).prod *
      (remaining.map fun v => 1 - probability v + probability v * factor r v).prod

theorem branch_identity (buying probability : V → ℚ) (factor : R → V → ℚ)
    (amplitude : R → ℚ) (fixedCost normalization : ℚ) (selected remaining : List V) (v : V) :
    potential buying probability factor amplitude fixedCost normalization selected (v :: remaining) =
      (1 - probability v) * potential buying probability factor amplitude fixedCost normalization selected remaining +
      probability v * potential buying probability factor amplitude fixedCost normalization (v :: selected) remaining := by
  unfold potential
  simp only [List.map_cons, List.sum_cons, List.prod_cons]
  have rows : (∑ r, amplitude r * (selected.map (factor r)).prod *
      ((1 - probability v + probability v * factor r v) *
        (remaining.map fun a => 1 - probability a + probability a * factor r a).prod)) =
      (1 - probability v) * (∑ r, amplitude r * (selected.map (factor r)).prod *
        (remaining.map fun a => 1 - probability a + probability a * factor r a).prod) +
      probability v * (∑ r, amplitude r * (factor r v * (selected.map (factor r)).prod) *
        (remaining.map fun a => 1 - probability a + probability a * factor r a).prod) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [rows]
  ring

/-- Fix a zero-probability variable to zero; otherwise choose the smaller of
the two explicit conditional expectations, breaking ties toward zero. -/
def choose (buying probability : V → ℚ) (factor : R → V → ℚ)
    (amplitude : R → ℚ) (fixedCost normalization : ℚ) : List V → List V → List V
  | selected, [] => selected
  | selected, v :: remaining =>
      if probability v = 0 ∨
          potential buying probability factor amplitude fixedCost normalization selected remaining ≤
            potential buying probability factor amplitude fixedCost normalization (v :: selected) remaining then
        choose buying probability factor amplitude fixedCost normalization selected remaining
      else choose buying probability factor amplitude fixedCost normalization (v :: selected) remaining
termination_by _ remaining => remaining.length

theorem choose_potential_le (buying probability : V → ℚ) (factor : R → V → ℚ)
    (amplitude : R → ℚ) (fixedCost normalization : ℚ)
    (valid : ∀ v, 0 ≤ probability v ∧ probability v ≤ 1) (remaining selected : List V) :
    potential buying probability factor amplitude fixedCost normalization
      (choose buying probability factor amplitude fixedCost normalization selected remaining) [] ≤
    potential buying probability factor amplitude fixedCost normalization selected remaining := by
  induction remaining generalizing selected with
  | nil => simp only [choose, le_refl]
  | cons v remaining ih =>
    have identity := branch_identity buying probability factor amplitude fixedCost normalization selected remaining v
    simp only [choose]
    split_ifs with branch
    · apply (ih selected).trans
      rcases branch with zero | smaller
      · simpa [zero] using identity.ge
      · have pv := valid v
        nlinarith
    · apply (ih (v :: selected)).trans
      have smaller : potential buying probability factor amplitude fixedCost normalization (v :: selected) remaining ≤
          potential buying probability factor amplitude fixedCost normalization selected remaining := le_of_not_ge (not_or.mp branch).2
      have pv := valid v
      nlinarith

theorem choose_mem (buying probability : V → ℚ) (factor : R → V → ℚ)
    (amplitude : R → ℚ) (fixedCost normalization : ℚ) (remaining selected : List V) (a : V) :
    a ∈ choose buying probability factor amplitude fixedCost normalization selected remaining →
      a ∈ selected ∨ a ∈ remaining := by
  induction remaining generalizing selected with
  | nil => simp [choose]
  | cons v remaining ih =>
    simp only [choose]
    split_ifs
    · intro ha
      rcases ih selected ha with hs | hr
      · exact Or.inl hs
      · exact Or.inr (List.mem_cons_of_mem v hr)
    · intro ha
      rcases ih (v :: selected) ha with hs | hr
      · rcases List.mem_cons.mp hs with heq | hs
        · exact Or.inr (List.mem_cons.mpr (Or.inl heq))
        · exact Or.inl hs
      · exact Or.inr (List.mem_cons_of_mem v hr)

theorem choose_nodup (buying probability : V → ℚ) (factor : R → V → ℚ)
    (amplitude : R → ℚ) (fixedCost normalization : ℚ) (remaining selected : List V) :
    (selected ++ remaining).Nodup →
      (choose buying probability factor amplitude fixedCost normalization selected remaining).Nodup := by
  induction remaining generalizing selected with
  | nil => simpa only [choose, List.append_nil] using (fun h => h)
  | cons v remaining ih =>
    intro hn
    obtain ⟨hs, hr, hdisj⟩ := List.nodup_append.mp hn
    obtain ⟨hv, ht⟩ := List.nodup_cons.mp hr
    have skip : (selected ++ remaining).Nodup := List.nodup_append.mpr
      ⟨hs, ht, fun a ha b hb => hdisj a ha b (List.mem_cons_of_mem v hb)⟩
    have take : ((v :: selected) ++ remaining).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨List.nodup_cons.mpr ⟨?_, hs⟩, ht, ?_⟩
      · intro hmem
        exact hdisj v hmem v (by simp) rfl
      · intro a ha b hb
        rcases List.mem_cons.mp ha with heq | ha
        · subst a
          intro heq
          subst b
          exact hv hb
        · exact hdisj a ha b (List.mem_cons_of_mem v hb)
    simp only [choose]
    split_ifs
    · exact ih selected skip
    · exact ih (v :: selected) take

theorem choose_zero_probability (buying probability : V → ℚ) (factor : R → V → ℚ)
    (amplitude : R → ℚ) (fixedCost normalization : ℚ) (remaining selected : List V) (a : V)
    (zero : probability a = 0) :
    a ∈ choose buying probability factor amplitude fixedCost normalization selected remaining →
      a ∈ selected := by
  induction remaining generalizing selected with
  | nil => simpa only [choose] using (fun h => h)
  | cons v remaining ih =>
    simp only [choose]
    split_ifs with branch
    · exact ih selected
    · intro ha
      rcases List.mem_cons.mp (ih (v :: selected) ha) with heq | hs
      · subst a
        exact False.elim ((not_or.mp branch).1 zero)
      · exact hs

end BuyAtBulk.ConditionalExpectation
