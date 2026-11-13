import Mathlib.Analysis.SpecialFunctions.Log.Basic
import BuyAtBulk.EdgeOnlyGap.Items.LocallySparse
import BuyAtBulk.EdgeOnlyGap.Items.RegularBase
import BuyAtBulk.EdgeOnlyGap.Items.MooreLogPolynomial

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Lemma 1 polynomial clause, p. 3: uniform exponent, nonempty regular bases. -/
theorem polynomialLift : ∃ C k : ℕ, 0 < C ∧
  ∀ (H : FiniteGraph) (d g T : ℕ), 4 ≤ d → 4 ≤ g → g ≤ T →
    RegularBase H d g →
    (g : ℝ) * Real.log d ≤ C * Real.log H.n ∧
    (liftA d)^g ≤ C * H.n^k ∧
    liftQ H.n d g T ≤ C * (H.n*T)^k := by
  obtain ⟨C, k, hC, hbound⟩ := mooreLogPolynomial
  refine ⟨1001*C, k+3, by positivity, ?_⟩
  intro H d g T hd hg hT base
  obtain ⟨_, hlog, hpow⟩ := hbound H d g hd hg base
  have hn : 1 ≤ H.n := base.1
  have ht : 1 ≤ T := by omega
  have hN : 1 ≤ H.n*T := Nat.mul_pos base.1 (by omega)
  have hnN : H.n ≤ H.n*T := by nlinarith
  have htN : T ≤ H.n*T := by nlinarith
  have hCC : C ≤ 1001*C := by omega
  refine ⟨?_, ?_, ?_⟩
  · exact hlog.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hCC)
      (Real.log_nonneg (by exact_mod_cast hn)))
  · exact hpow.trans (Nat.mul_le_mul hCC (Nat.pow_le_pow_right hn (by omega)))
  · have hprod : H.n * H.n^k * T^2 ≤ (H.n*T) * (H.n*T)^k * (H.n*T)^2 :=
      Nat.mul_le_mul (Nat.mul_le_mul hnN (Nat.pow_le_pow_left hnN k))
        (Nat.pow_le_pow_left htN 2)
    calc
      liftQ H.n d g T ≤ 1000*H.n*T^2*(C*H.n^k) := Nat.mul_le_mul_left _ hpow
      _ = (1000*C)*(H.n*H.n^k*T^2) := by ring
      _ ≤ (1000*C)*((H.n*T)*(H.n*T)^k*(H.n*T)^2) := Nat.mul_le_mul_left _ hprod
      _ = (1000*C)*(H.n*T)^(k+3) := by ring
      _ ≤ (1001*C)*(H.n*T)^(k+3) := Nat.mul_le_mul_right _ (by omega)

end BuyAtBulk.EdgeOnlyGap
