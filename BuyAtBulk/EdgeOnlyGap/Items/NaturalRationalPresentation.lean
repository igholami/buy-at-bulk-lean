import BuyAtBulk.EdgeOnlyGap.Items.NaturalStored
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofCRowEvaluation
import BuyAtBulk.EdgeOnlyGap.Items.NaturalDecode

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit scalar-domain correspondence for equation (2), p. 1, used in Theorem 1: exact rational feasibility/objective correspondence and unit-box consequence, with no nonempty-resource/request/path premise. -/
theorem naturalRationalPresentation (I : BuyAtBulk.Instance)
    (z : Fin (I.resourceCount + I.requestCount * I.pathCount) → ℚ) :
    ((naturalStored I).problem.Feasible z ↔ I.Feasible (naturalDecode I z)) ∧
    (naturalStored I).problem.objective z = lpObjective I (naturalDecode I z) ∧
    ((naturalStored I).problem.Feasible z → ∀ j, 0 ≤ z j ∧ z j ≤ 1) := by
  classical
  have rows : (naturalStored I).problem.Feasible z ↔
      ∀ row : NaturalLPRow I,
        (∑ j, (naturalRowCoefficient I row j : ℚ) * z j) ≤ (naturalRowBound I row : ℚ) := by
    constructor
    · intro hz row
      have hh := hz (Fintype.equivFin (NaturalLPRow I) row)
      simpa [BuyAtBulk.PolynomialLP.Stored.problem, BuyAtBulk.PolynomialLP.rowForm_apply,
        naturalStored] using hh
    · intro hz i
      have hh := hz ((Fintype.equivFin (NaturalLPRow I)).symm i)
      simpa [BuyAtBulk.PolynomialLP.Stored.problem, BuyAtBulk.PolynomialLP.rowForm_apply,
        naturalStored] using hh
  have heval := ProofC.rowEvaluation (K := ℚ) I z
  simp only [Rat.cast_id] at heval
  simp_rw [heval] at rows
  have iff_feas : (naturalStored I).problem.Feasible z ↔ I.Feasible (naturalDecode I z) := by
    rw [rows]
    constructor
    · intro hr
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro a
        have lo := hr (.openingLower a)
        have hi := hr (.openingUpper a)
        simp only [naturalRowBound, Rat.cast_zero, Rat.cast_one] at lo hi
        exact ⟨by simpa [naturalDecode] using (neg_nonpos.mp lo), hi⟩
      · intro i p
        have lo := hr (.flowLower i p)
        simp only [naturalRowBound, Rat.cast_zero] at lo
        exact neg_nonpos.mp lo
      · intro i p h
        have up := hr (.forbidden i p)
        have lo := hr (.flowLower i p)
        simp [naturalRowBound, h] at up lo
        change z (naturalCoordinateEquiv I (.inr (i,p))) = 0
        linarith
      · intro i
        have up := hr (.unitUpper i)
        have lo := hr (.unitLower i)
        simp [naturalRowBound] at up lo
        change (∑ p, z (naturalCoordinateEquiv I (.inr (i,p)))) = 1
        linarith
      · intro i a
        have hc := hr (.capacity i a)
        simp only [naturalRowBound, Rat.cast_zero] at hc
        change (∑ p, if a ∈ I.uses p then z (naturalCoordinateEquiv I (.inr (i,p))) else 0) ≤
          z (naturalCoordinateEquiv I (.inl a))
        linarith
    · rintro ⟨hb, hn, hf, hu, hc⟩ row
      cases row with
      | openingLower a => simpa [naturalRowBound, naturalDecode] using (neg_nonpos.mpr (hb a).1)
      | openingUpper a => simpa [naturalRowBound, naturalDecode] using (hb a).2
      | flowLower i p => simpa [naturalRowBound, naturalDecode] using (neg_nonpos.mpr (hn i p))
      | forbidden i p =>
        by_cases h : I.allowed i p = false
        · simp [naturalRowBound, h, show z (naturalCoordinateEquiv I (.inr (i,p))) = 0 from hf i p h]
        · simp [naturalRowBound, h]
      | unitUpper i => simpa [naturalRowBound, naturalDecode] using (hu i).le
      | unitLower i =>
        have he : (∑ p, z (naturalCoordinateEquiv I (.inr (i,p)))) = 1 := hu i
        simp [naturalRowBound, he]
      | capacity i a =>
        have hh : (∑ p, if a ∈ I.uses p then z (naturalCoordinateEquiv I (.inr (i,p))) else 0) ≤
            z (naturalCoordinateEquiv I (.inl a)) := hc i a
        simp only [naturalRowBound, Rat.cast_zero]
        linarith
  refine ⟨iff_feas, ?_, ?_⟩
  · change BuyAtBulk.PolynomialLP.rowForm (naturalStored I).objective z = _
    rw [BuyAtBulk.PolynomialLP.rowForm_apply]
    rw [← (naturalCoordinateEquiv I).sum_comp]
    simp [naturalStored, Fintype.sum_sum_type, Fintype.sum_prod_type,
      lpObjective, naturalDecode, BuyAtBulk.Instance.buyingCost, BuyAtBulk.Instance.rentalCost, BuyAtBulk.Instance.fractionalLength,
      Finset.mul_sum, mul_assoc]
  · intro hz j
    have hf := iff_feas.mp hz
    obtain ⟨a, rfl⟩ := (naturalCoordinateEquiv I).surjective j
    cases a with
    | inl a => exact hf.1 a
    | inr ip =>
      rcases ip with ⟨i,p⟩
      refine ⟨hf.2.1 i p, ?_⟩
      have hs := Finset.single_le_sum (s := Finset.univ)
        (f := fun p => z (naturalCoordinateEquiv I (.inr (i,p))))
        (fun q _ => hf.2.1 i q) (Finset.mem_univ p)
      have hu : (∑ p, z (naturalCoordinateEquiv I (.inr (i,p)))) = 1 := hf.2.2.2.1 i
      linarith


end BuyAtBulk.EdgeOnlyGap
