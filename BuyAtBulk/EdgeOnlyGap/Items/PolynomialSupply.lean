import BuyAtBulk.EdgeOnlyGap.Items.Parameters
import BuyAtBulk.EdgeOnlyGap.Items.RegularBase
import BuyAtBulk.EdgeOnlyGap.Items.PolynomialLift
import BuyAtBulk.EdgeOnlyGap.Items.Handshaking

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 5: uniform polynomial in request count, including private leaves. -/
theorem polynomialSupply : ∃ C k : ℕ, 0 < C ∧
  ∀ (H : FiniteGraph) (g : ℕ), 4 ≤ g → RegularBase H g g →
  let q := liftQ H.n g g (threshold H g)
  H.n*(q+1)+2*requests H ≤ C*(requests H)^k ∧
  q*(H.n+requests H)+2*requests H ≤ C*(requests H)^k := by
  obtain ⟨C, k, hC, hb⟩ := polynomialLift
  refine ⟨2*C+3, 3*k+2, by omega, ?_⟩
  intro H g hg base
  let h := requests H
  have hs : 2*h = H.n*g := handshaking H g g base
  have hnv := H.graph.degree_lt_card_verts (⟨0, base.1⟩ : Fin H.n)
  rw [base.2.1] at hnv
  simp only [Fintype.card_fin] at hnv
  have hng : 2 ≤ H.n := by omega
  have hh : 1 ≤ h := by nlinarith
  have hnH : H.n ≤ h := by nlinarith
  have hgH : g ≤ h := by nlinarith
  have hT : g ≤ threshold H g := by dsimp [threshold]; change g ≤ h*g; nlinarith
  have hq := (hb H g g (threshold H g) hg hg hT base).2.2
  have hprod : H.n * threshold H g ≤ h^3 := by
    dsimp [threshold]
    change H.n * (h*g) ≤ h^3
    have hp := Nat.mul_le_mul hnH (Nat.mul_le_mul_left h hgH)
    nlinarith
  have hq' : liftQ H.n g g (threshold H g) ≤ C*h^(3*k) := by
    calc
      _ ≤ C*(H.n*threshold H g)^k := hq
      _ ≤ C*(h^3)^k := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hprod k)
      _ = C*h^(3*k) := by rw [← pow_mul]
  have hu : h ≤ h^(3*k+2) := by
    simpa using (Nat.pow_le_pow_right hh (show 1 ≤ 3*k+2 by omega))
  have hqh : liftQ H.n g g (threshold H g)*h ≤ C*h^(3*k+2) := by
    calc
      _ ≤ (C*h^(3*k))*h := Nat.mul_le_mul_right h hq'
      _ = C*h^(3*k+1) := by ring
      _ ≤ C*h^(3*k+2) := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hh (by omega))
  dsimp only
  change H.n*(liftQ H.n g g (threshold H g)+1)+2*h ≤ (2*C+3)*h^(3*k+2) ∧
    liftQ H.n g g (threshold H g)*(H.n+h)+2*h ≤ (2*C+3)*h^(3*k+2)
  constructor
  · have hp := Nat.mul_le_mul_right (liftQ H.n g g (threshold H g)+1) hnH
    nlinarith
  · have hp := Nat.mul_le_mul_left (liftQ H.n g g (threshold H g)) hnH
    nlinarith

end BuyAtBulk.EdgeOnlyGap
