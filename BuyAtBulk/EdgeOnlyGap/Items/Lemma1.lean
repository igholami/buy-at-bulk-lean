import BuyAtBulk.EdgeOnlyGap.Items.EmptyLift
import BuyAtBulk.EdgeOnlyGap.Items.PrescribedQBounds
import BuyAtBulk.EdgeOnlyGap.Items.WitnessUnionBound
import BuyAtBulk.EdgeOnlyGap.Items.GeometricEstimate
import BuyAtBulk.EdgeOnlyGap.Items.LocallySparse
import BuyAtBulk.EdgeOnlyGap.Items.GirthAtLeast

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Lemma 1, pp. 2–3: maximum degree is an upper bound; empty graph included. -/
theorem lemma1 (H : FiniteGraph) (d g T : ℕ) (hd : 4 ≤ d) (hg : 4 ≤ g)
    (degree : ∀ v, H.graph.degree v ≤ d) (girth : GirthAtLeast H g) (hT : g ≤ T) :
  ∃ π : Lift H (liftQ H.n d g T), LocallySparse H (liftQ H.n d g T) g T π := by
  classical
  rcases Nat.eq_zero_or_pos H.n with hn0 | hn
  · exact emptyLift H d g T hn0
  · let q := liftQ H.n d g T
    have hq8 : 8 * T ≤ q := (prescribedQBounds H.n d g T hn hd hg hT).2.1
    have hub := witnessUnionBound H q d g T hd hg hq8 hT degree girth
    have hgeom := geometricEstimate H.n d g T hn hd hg hT
    rcases hgeom with ⟨_, _, _, h4, h5, h6, h7⟩
    have hprob_lt : liftProbability H q (fun π => ¬ LocallySparse H q g T π) < 1 :=
      lt_of_le_of_lt (le_trans hub (le_trans h4 (le_trans h5 h6))) h7
    by_contra h_none
    push_neg at h_none
    letI : Nonempty (Lift H q) := ⟨fun _ => Equiv.refl _⟩
    have hc : Nat.card {π : Lift H q // ¬LocallySparse H q g T π} = Nat.card (Lift H q) :=
      Nat.card_congr
        { toFun := fun x => x.val
          invFun := fun π => ⟨π, h_none π⟩
          left_inv := fun x => rfl
          right_inv := fun π => rfl }
    have hprob_one : liftProbability H q (fun π => ¬ LocallySparse H q g T π) = 1 := by
      unfold liftProbability finiteProbability
      simp only [← Nat.card_eq_fintype_card]
      rw [hc]
      exact div_self (by exact_mod_cast (Nat.card_pos (α := Lift H q)).ne')
    linarith

end BuyAtBulk.EdgeOnlyGap
