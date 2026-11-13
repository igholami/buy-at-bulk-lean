import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import BuyAtBulk.EdgeOnlyGap.Items.Parameters

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit prescribed-q side conditions, pp. 2–3; nonempty-base branch of Lemma 1. -/
theorem prescribedQBounds (n d g T : ℕ) (hn : 0 < n) (hd : 4 ≤ d)
    (hg : 4 ≤ g) (hT : g ≤ T) :
  0 < liftQ n d g T ∧ 8*T ≤ liftQ n d g T ∧
    (Nat.ceil (1000*(n:ℝ)*T^2*(liftA d:ℝ)^g)) = liftQ n d g T := by
  have hTpos : 0 < T := by omega
  have hApos : 0 < liftA d := by unfold liftA; positivity
  have hAg : 1 ≤ (liftA d) ^ g := Nat.one_le_pow g (liftA d) hApos
  refine ⟨?_, ?_, ?_⟩
  · unfold liftQ
    positivity
  · unfold liftQ
    have h1 : 8 * T ≤ 1000 * 1 * (T * 1) * 1 := by omega
    have h2 : 1000 * 1 * (T * 1) * 1 ≤ 1000 * n * T ^ 2 * (liftA d) ^ g := by
      rw [sq]
      exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl hn) (Nat.mul_le_mul le_rfl hTpos)) hAg
    exact le_trans h1 h2
  · have hcast : (1000 * (n : ℝ) * (T : ℝ) ^ 2 * (liftA d : ℝ) ^ g) = ((liftQ n d g T : ℕ) : ℝ) := by
      unfold liftQ
      push_cast
      ring
    rw [hcast, Nat.ceil_natCast]

end BuyAtBulk.EdgeOnlyGap
