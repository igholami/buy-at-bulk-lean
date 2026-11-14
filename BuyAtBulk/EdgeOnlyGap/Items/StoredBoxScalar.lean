import BuyAtBulk.Computation.PolynomialLP.ExactFromSlack
import BuyAtBulk.Computation.PolynomialLP.IntegerData
import Mathlib.Algebra.Order.Archimedean.Real.Basic

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit scalar-domain correspondence for equation (2), p. 1, used in Theorem 1: bounded real feasibility iff bounded rational feasibility, including n=0 and m=0. -/
theorem storedBoxScalar {n m : ℕ} (input : BuyAtBulk.PolynomialLP.Stored (n := n) (m := m)) :
    (∃ x : Fin n → ℝ, BuyAtBulk.PolynomialLP.RealFeasible input x ∧ ∀ j, 0 ≤ x j ∧ x j ≤ 1) ↔
    (∃ y : Fin n → ℚ, input.problem.Feasible y ∧ ∀ j, 0 ≤ y j ∧ y j ≤ 1)  := by
  classical
  constructor
  · rintro ⟨x, hx, hbox⟩
    let L := BuyAtBulk.PolynomialLP.integerL input
    let H := BuyAtBulk.PolynomialLP.integerH input
    let ε := BuyAtBulk.PolynomialLP.feasibilitySlack n L
    have he : (0 : ℝ) < (ε : ℝ) := by
      exact_mod_cast BuyAtBulk.PolynomialLP.feasibilitySlack_pos n L
    let δ : ℝ := (ε : ℝ) / ((n : ℝ) * H + 1)
    have hH : (0 : ℝ) < H := by
      exact_mod_cast BuyAtBulk.PolynomialLP.integerH_positive input
    have hd : 0 < δ := div_pos he (by positivity)
    have hde : δ ≤ (ε : ℝ) := by
      dsimp [δ]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < n * H + 1)).2
      apply le_mul_of_one_le_right he.le
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith [mul_nonneg hn hH.le]
    have approx : ∀ j : Fin n, ∃ q : ℚ, |(q : ℝ) - x j| ≤ δ := by
      intro j
      obtain ⟨q, hq, hq'⟩ := exists_rat_btwn (show x j - δ < x j + δ by linarith)
      exact ⟨q, abs_le.mpr ⟨by linarith, by linarith⟩⟩
    choose q hq using approx
    let point : Vector ℚ n := Vector.ofFn q
    have hi := (BuyAtBulk.PolynomialLP.integerize_realFeasible input x).2 hx
    have ha (i : Fin m) (j : Fin n) :
        |((BuyAtBulk.PolynomialLP.integerize input).coefficients[i.val][j.val] : ℝ)| ≤ H := by
      rw [BuyAtBulk.PolynomialLP.integerize_coefficient_int]
      have hb := (BuyAtBulk.PolynomialLP.integerA_bound input i j).le
      have hb' : |BuyAtBulk.PolynomialLP.integerA input i j| ≤ (H : ℤ) := by
        have hh : ((BuyAtBulk.PolynomialLP.integerA input i j).natAbs : ℤ) ≤ H := by
          exact_mod_cast hb
        simpa only [Int.natCast_natAbs] using hh
      exact_mod_cast hb'
    have hbox' : ∀ j : Fin n, -ε ≤ point[j.val] ∧ point[j.val] ≤ 1 + ε := by
      intro j
      have a := (abs_le.mp (hq j)).1
      have b := (abs_le.mp (hq j)).2
      have lo : -(ε : ℝ) ≤ (q j : ℝ) := by linarith [(hbox j).1]
      have up : (q j : ℝ) ≤ 1 + (ε : ℝ) := by linarith [(hbox j).2]
      simpa [point] using (show -ε ≤ q j ∧ q j ≤ 1 + ε by exact_mod_cast And.intro lo up)
    have hrows : ∀ i : Fin m,
        BuyAtBulk.PolynomialLP.rowForm (BuyAtBulk.PolynomialLP.integerize input).coefficients[i.val]
          (fun j => point[j.val]) ≤ (BuyAtBulk.PolynomialLP.integerize input).bounds[i.val] + ε := by
      intro i
      have terms (j : Fin n) :
          ((BuyAtBulk.PolynomialLP.integerize input).coefficients[i.val][j.val] : ℝ) *
            ((q j : ℝ) - x j) ≤ (H : ℝ) * δ := by
        calc
          _ ≤ |((BuyAtBulk.PolynomialLP.integerize input).coefficients[i.val][j.val] : ℝ) *
            ((q j : ℝ) - x j)| := le_abs_self _
          _ = _ := abs_mul _ _
          _ ≤ _ := mul_le_mul (ha i j) (hq j) (abs_nonneg _) hH.le
      have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => terms j)
      have hbudget : (n : ℝ) * ((H : ℝ) * δ) ≤ (ε : ℝ) := by
        have hid : δ * ((n : ℝ) * H + 1) = (ε : ℝ) :=
          div_mul_cancel₀ _ (by positivity)
        nlinarith
      have result : (∑ j : Fin n,
          ((BuyAtBulk.PolynomialLP.integerize input).coefficients[i.val][j.val] : ℝ) * (q j : ℝ)) ≤
          ((BuyAtBulk.PolynomialLP.integerize input).bounds[i.val] : ℝ) + (ε : ℝ) := by
        simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul] at hs
        linarith [hi i]
      rw [BuyAtBulk.PolynomialLP.rowForm_apply]
      simp only [point, Vector.getElem_ofFn]
      exact_mod_cast result
    obtain ⟨y, hy, hybox⟩ := BuyAtBulk.PolynomialLP.exact_of_uniform_slack
      (BuyAtBulk.PolynomialLP.integerize input)
      (BuyAtBulk.PolynomialLP.integerA input) (BuyAtBulk.PolynomialLP.integerB input) L
      (BuyAtBulk.PolynomialLP.integerize_coefficient_int input)
      (BuyAtBulk.PolynomialLP.integerize_bound_int input)
      (fun i j => (BuyAtBulk.PolynomialLP.integerA_bound input i j).le)
      (fun i => (BuyAtBulk.PolynomialLP.integerB_bound input i).le) point hbox' hrows
    exact ⟨y, (BuyAtBulk.PolynomialLP.integerize_feasible input y).1 hy, hybox⟩
  · rintro ⟨y, hy, hbox⟩
    refine ⟨fun j => (y j : ℝ), ?_, ?_⟩
    · intro i
      have h := hy i
      change BuyAtBulk.PolynomialLP.rowForm input.coefficients[i.val] y ≤ input.bounds[i.val] at h
      simp only [BuyAtBulk.PolynomialLP.rowForm_apply] at h
      change (∑ j : Fin n, (input.coefficients[i.val][j.val] : ℝ) * (y j : ℝ)) ≤
        (input.bounds[i.val] : ℝ)
      exact_mod_cast h
    · intro j
      change 0 ≤ (y j : ℝ) ∧ (y j : ℝ) ≤ 1
      exact_mod_cast hbox j

end BuyAtBulk.EdgeOnlyGap
