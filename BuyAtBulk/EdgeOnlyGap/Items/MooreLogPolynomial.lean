import Mathlib.Analysis.SpecialFunctions.Log.Basic
import BuyAtBulk.EdgeOnlyGap.Items.Parameters
import BuyAtBulk.EdgeOnlyGap.Items.RegularBase
import BuyAtBulk.EdgeOnlyGap.Items.MooreBound

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Intermediate estimates, p. 3: A≤d^5, g log d=O(log n), polynomial A^g. -/
theorem mooreLogPolynomial : ∃ C k : ℕ, 0<C ∧
  ∀ (H : FiniteGraph) (d g : ℕ), 4 ≤ d → 4 ≤ g → RegularBase H d g →
    liftA d ≤ d^5 ∧ (g:ℝ)*Real.log d ≤ C*Real.log H.n ∧
    (liftA d)^g ≤ C*H.n^k := by
  refine ⟨12, 60, by norm_num, ?_⟩
  intro H d g hd hg base
  let r := (g - 1) / 2
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hgr : g ≤ 6 * r := by dsimp [r]; omega
  have hdsub : 3 ≤ d - 1 := by omega
  have hdrepr : d - 1 + 1 = d := by omega
  have hdsq : d ≤ (d - 1)^2 := by nlinarith
  have hA : liftA d ≤ d^5 := by
    have hcube : 64 ≤ d^3 := by
      have hh := Nat.pow_le_pow_left hd 3
      norm_num at hh ⊢
      exact hh
    dsimp [liftA]
    calc
      64 * d^2 ≤ d^3 * d^2 := Nat.mul_le_mul_right _ hcube
      _ = d^5 := by ring
  have hmoore : (d - 1)^r ≤ H.n := mooreBound H d g hd hg base
  have hdm : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
  have hn : (0 : ℝ) < H.n := by exact_mod_cast base.1
  have hdcast : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hlogd : Real.log (d : ℝ) ≤ 2 * Real.log ((d - 1 : ℕ) : ℝ) := by
    have hh := Real.log_le_log hdcast
      (show (d : ℝ) ≤ ((d - 1 : ℕ) : ℝ)^2 by exact_mod_cast hdsq)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hlogn : (r : ℝ) * Real.log ((d - 1 : ℕ) : ℝ) ≤ Real.log H.n := by
    have hh := Real.log_le_log (pow_pos hdm r)
      (show (((d - 1 : ℕ) : ℝ)^r) ≤ H.n by exact_mod_cast hmoore)
    simpa only [Real.log_pow] using hh
  have hlogdm : 0 ≤ Real.log ((d - 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ d - 1 by omega))
  refine ⟨hA, ?_, ?_⟩
  · have hgr' : (g : ℝ) ≤ 6 * (r : ℝ) := by exact_mod_cast hgr
    calc
      (g : ℝ) * Real.log d ≤ (g : ℝ) * (2 * Real.log ((d - 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogd (Nat.cast_nonneg g)
      _ ≤ (6 * (r : ℝ)) * (2 * Real.log ((d - 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hgr' (by positivity)
      _ ≤ 12 * Real.log H.n := by nlinarith
  · calc
      (liftA d)^g ≤ (d^5)^g := Nat.pow_le_pow_left hA g
      _ = d^(5*g) := (pow_mul d 5 g).symm
      _ ≤ ((d-1)^2)^(5*g) := Nat.pow_le_pow_left hdsq _
      _ = (d-1)^(10*g) := by rw [← pow_mul]; congr 1; ring
      _ ≤ (d-1)^(60*r) := Nat.pow_le_pow_right (by omega) (by omega)
      _ = ((d-1)^r)^60 := by rw [← pow_mul]; congr 1; ring
      _ ≤ H.n^60 := Nat.pow_le_pow_left hmoore _
      _ ≤ 12 * H.n^60 := by omega

end BuyAtBulk.EdgeOnlyGap
