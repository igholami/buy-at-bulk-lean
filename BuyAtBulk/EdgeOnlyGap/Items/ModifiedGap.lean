import BuyAtBulk.EdgeOnlyGap.Items.FinalFiniteOptima

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit unchanged linear-in-g gap after both modifications, p. 5. -/
theorem modifiedGap (H : FiniteGraph) (q g : ℕ) (π : Lift H q)
    (hg : 4 ≤ g) (hq : 0 < q) (base : RegularBase H g g)
    (sparse : LocallySparse H q g (threshold H g) π) :
  let D := privateLeaves (positiveData H q g π (by omega))
    (1/(10*(requests H:ℚ))) (by positivity)
  ∃ opt lp : ℚ, ExactOptima D opt lp ∧ 0 < lp ∧ (g:ℚ)/24 ≤ opt/lp  := by
  dsimp only
  obtain ⟨opt, lp, ho, hlp, _, hup, hopt, _⟩ := finalFiniteOptima H q g π hg hq base sparse
  refine ⟨opt, lp, ho, hlp, ?_⟩
  apply (le_div_iff₀ hlp).2
  have hn : (1 : ℚ) ≤ H.n := by exact_mod_cast base.1
  have hg' : (0 : ℚ) ≤ g := Nat.cast_nonneg g
  calc
    (g : ℚ)/24 * lp ≤ (g : ℚ)/24 * (2*H.n+17/5) :=
      mul_le_mul_of_nonneg_left hup (by positivity)
    _ ≤ (H.n : ℚ)*g/4 := by nlinarith [mul_nonneg hg' (sub_nonneg.mpr hn)]
    _ ≤ opt := hopt

end BuyAtBulk.EdgeOnlyGap
