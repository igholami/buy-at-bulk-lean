import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBFractionalWitness
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBWitnessMass
import BuyAtBulk.EdgeOnlyGap.Items.PositiveModification
import BuyAtBulk.EdgeOnlyGap.Items.SupplySizes
import Mathlib.Algebra.BigOperators.Field

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofB
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 800000 in
/-- The displayed split witness has the exact perturbed buying and rental costs. -/
theorem positiveFractionalWitness (H : FiniteGraph) (q d g : ℕ) (π : Lift H q)
    (hd : 0 < d) (hq : 0 < q) (base : RegularBase H d g) :
    ∃ f : (positiveData H q d π hd).toInstance.FractionalSolution,
      (positiveData H q d π hd).toInstance.Feasible f ∧
      (positiveData H q d π hd).toInstance.buyingCost f = H.n + 1 ∧
      (positiveData H q d π hd).toInstance.rentalCost f = H.n + 2 := by
  classical
  let D := supplyData H q d π hd
  let P := positiveData H q d π hd
  let f₀ := fractionalWitness H q d π hd
  let f : P.toInstance.FractionalSolution := ⟨f₀.opening, f₀.flow⟩
  have h0 := fractionalWitnessCosts H d g q base hd hq π
  have hhs : 2 * requests H = H.n * d := handshaking H d g base
  have hmpos : 0 < requests H := by have := Nat.mul_pos base.1 hd; omega
  have hm : (requests H : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hmpos)
  have hqne : (q : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  have hdne : (d : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  let m : ℚ := requests H
  let α : ℚ := 1 - (d : ℚ) / (2 * m)
  have hcb (a : Fin D.resourceCount) : P.buying a = (1 - 1/m) * D.buying a + 1/m := by
    change (if coreResource H q d π hd a then 1/m else D.buying a) = _
    have hb : D.buying a = if coreResource H q d π hd a then 0 else 1 := by
      simp only [D, supplyData, coreResource, Sum.inr.injEq]
    rw [hb]
    split_ifs <;> ring
  have hcl (a : Fin D.resourceCount) : P.length a = α * D.length a + 1/m := by
    change (if coreResource H q d π hd a then D.length a else 1/m) = _
    have hl : D.length a = if coreResource H q d π hd a then 2/(d : ℚ) else 0 := by
      simp only [D, supplyData, coreResource, Sum.inr.injEq]
    rw [hl]
    split_ifs <;> dsimp [α, m] <;> field_simp [hm, hdne] <;> ring
  have hb0 : D.toInstance.buyingCost f₀ = H.n := h0.2.1
  have hr0 : (∑ i : Fin D.requestCount, D.toInstance.fractionalLength f₀ i) = H.n := by
    have h := h0.2.2.1
    change (∑ i : Fin D.requestCount, 1 * D.toInstance.fractionalLength f₀ i) = H.n at h
    simpa only [one_mul] using h
  have hopen : (∑ a, f₀.opening a) = (D.resourceCount : ℚ) / q := by
    change (∑ a : Fin D.resourceCount, (1 : ℚ) / q) = _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hpath (p : Fin D.toInstance.pathCount) : P.toInstance.pathLength p =
      α * D.toInstance.pathLength p + ((D.toInstance.uses p).card : ℚ)/m := by
    change (∑ a ∈ D.toInstance.uses p, P.length a) = _
    trans ∑ a ∈ D.toInstance.uses p, (α * D.length a + 1/m)
    · exact Finset.sum_congr rfl (fun a _ => hcl a)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    unfold BuyAtBulk.Instance.pathLength
    ring
  have hfrac (i : Fin D.requestCount) : P.toInstance.fractionalLength f i =
      α * D.toInstance.fractionalLength f₀ i + 3/m := by
    change (∑ p : Fin D.toInstance.pathCount, P.toInstance.pathLength p * f₀.flow i p) = _
    trans ∑ p : Fin D.toInstance.pathCount, (α * (D.toInstance.pathLength p * f₀.flow i p) +
      (((D.toInstance.uses p).card : ℚ) * f₀.flow i p)/m)
    · apply Finset.sum_congr rfl
      intro p _
      rw [hpath]
      ring
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
    have hw := witnessMass H q d π hd hq i
    change (∑ p, ((D.toInstance.uses p).card : ℚ) * f₀.flow i p) = 3 at hw
    rw [hw]
    rfl
  refine ⟨f, h0.1, ?_, ?_⟩
  · change (∑ a : Fin D.resourceCount, P.buying a * f₀.opening a) = _
    trans (1 - 1/m) * D.toInstance.buyingCost f₀ + (∑ a, f₀.opening a)/m
    · trans ∑ a, ((1 - 1/m) * (D.buying a * f₀.opening a) + f₀.opening a/m)
      · apply Finset.sum_congr rfl
        intro a _
        rw [hcb]
        ring
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
      rfl
    rw [hb0, hopen]
    have hs : D.resourceCount = q * (H.n + requests H) := (supplySizes H q d π hd).2
    rw [hs]
    push_cast
    dsimp [m]
    field_simp [hm, hqne]
    ring
  · change (∑ i : Fin D.requestCount, 1 * P.toInstance.fractionalLength f i) = _
    simp only [one_mul]
    trans ∑ i : Fin D.requestCount, (α * D.toInstance.fractionalLength f₀ i + 3/m)
    · exact Finset.sum_congr rfl (fun i _ => hfrac i)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hr0, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    change α * (H.n : ℚ) + (requests H : ℚ) * (3/m) = H.n + 2
    have hh : 2 * (requests H : ℚ) = (H.n : ℚ) * d := by exact_mod_cast hhs
    dsimp [α, m]
    field_simp [hm]
    nlinarith

end BuyAtBulk.EdgeOnlyGap.ProofB
