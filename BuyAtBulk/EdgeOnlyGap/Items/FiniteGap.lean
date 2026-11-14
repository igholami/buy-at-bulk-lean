import BuyAtBulk.EdgeOnlyGap.Items.LPPositive
import BuyAtBulk.EdgeOnlyGap.Items.InitialOptima
import BuyAtBulk.EdgeOnlyGap.Items.IntegralLowerBound

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 5: the actual OPT/LP ratio for d=g. -/
theorem finiteGap (H : FiniteGraph) (q g : ℕ) (π : Lift H q) (hg : 4 ≤ g)
    (base : RegularBase H g g) (hq : 0 < q)
    (sparse : LocallySparse H q g (threshold H g) π) :
  ∃ opt lp : ℚ, ExactOptima (supplyData H q g π (by omega)) opt lp ∧
    0 < lp ∧ (H.n:ℚ)*g/4 ≤ opt ∧ lp ≤ 2*H.n ∧ (g:ℚ)/8 ≤ opt/lp  := by
  obtain ⟨opt, lp, ho, hlp, _, hup, hlo⟩ := initialOptima H q g g π hg hg hq base sparse
  have hg' : (0 : ℚ) ≤ g := Nat.cast_nonneg g
  have hmin : min ((g : ℚ)/2) ((g : ℚ)/4) = (g : ℚ)/4 :=
    min_eq_right (by linarith)
  rw [hmin] at hlo
  have hlo' : (H.n : ℚ)*g/4 ≤ opt := by nlinarith [hlo]
  refine ⟨opt, lp, ho, hlp, hlo', hup, ?_⟩
  apply (le_div_iff₀ hlp).2
  calc
    (g : ℚ)/8 * lp ≤ (g : ℚ)/8 * (2*H.n) :=
      mul_le_mul_of_nonneg_left hup (by positivity)
    _ = (H.n : ℚ)*g/4 := by ring
    _ ≤ opt := hlo'

end BuyAtBulk.EdgeOnlyGap
