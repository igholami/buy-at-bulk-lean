import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBPositiveFractionalWitness
import BuyAtBulk.EdgeOnlyGap.Items.PositiveModification
import BuyAtBulk.EdgeOnlyGap.Items.RegularBase
import BuyAtBulk.EdgeOnlyGap.Items.Optima
import BuyAtBulk.EdgeOnlyGap.Items.Lemma2
import BuyAtBulk.EdgeOnlyGap.Items.Handshaking
import Mathlib.Tactic.Linarith

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 800000 in
/-- P. 5: feasible witness costs 2n+3; positivity and cost monotonicity. -/
theorem positiveWitness (H : FiniteGraph) (q d g : ℕ) (π : Lift H q) (hd : 0 < d)
    (hq : 0 < q) (base : RegularBase H d g) :
  let D := supplyData H q d π hd
  let Dpos := positiveData H q d π hd
  (∀ a, 0 < Dpos.buying a ∧ 0 < Dpos.length a) ∧
  (∃ f : Dpos.toInstance.FractionalSolution, Dpos.toInstance.Feasible f ∧
    Dpos.toInstance.buyingCost f = H.n+1 ∧ Dpos.toInstance.rentalCost f = H.n+2) ∧
  (∀ r : Dpos.toInstance.IntegralRouting, ∃ s : D.toInstance.IntegralRouting,
    integralObjective D.toInstance s ≤ integralObjective Dpos.toInstance r) ∧
  (∀ f : Dpos.toInstance.FractionalSolution, Dpos.toInstance.Feasible f →
    ∃ f₀ : D.toInstance.FractionalSolution, D.toInstance.Feasible f₀ ∧
      lpObjective D.toInstance f₀ ≤ lpObjective Dpos.toInstance f) := by
  classical
  intro D Dpos
  let G := supplyGraph H q π
  let enum : Fin D.resourceCount ≃ G.edgeSet := (Fintype.equivFin G.edgeSet).symm
  let req : Fin D.requestCount ≃ Edges H := (Fintype.equivFin (Edges H)).symm
  have hhs : 2 * requests H = H.n * d := handshaking H d g base
  have hreq_pos : 0 < requests H := by
    have hprod := Nat.mul_pos base.1 hd
    omega
  have hreq_rat_pos : (0 : ℚ) < (requests H : ℚ) := by exact_mod_cast hreq_pos
  have hreq_ne : (requests H : ℚ) ≠ 0 := ne_of_gt hreq_rat_pos
  have hd_pos : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  have hd_ne : (d : ℚ) ≠ 0 := ne_of_gt hd_pos
  have hq_pos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hq_ne : (q : ℚ) ≠ 0 := ne_of_gt hq_pos
  have hcore_iff : ∀ a, coreResource H q d π hd a ↔
      ∃ v w : Fin H.n × Fin q, (enum a).val = s(Sum.inr v, Sum.inr w) := by
    intro a
    unfold coreResource
    change (∃ v w : Fin H.n × Fin q, (Sum.inr (enum a).val : SupplyVertex H q ⊕ Sym2 (SupplyVertex H q)) =
      Sum.inr (s(Sum.inr v, Sum.inr w))) ↔ _
    simp
  have hbuy_pos : ∀ a, 0 < Dpos.buying a ∧ 0 < Dpos.length a := by
    intro a
    change (0 < if coreResource H q d π hd a then 1 / (requests H : ℚ) else D.buying a) ∧
           (0 < if coreResource H q d π hd a then D.length a else 1 / (requests H : ℚ))
    by_cases hc : coreResource H q d π hd a
    · simp only [hc, ↓reduceIte]
      have hlen : D.length a = 2 / (d : ℚ) := by
        change (if ∃ v w : Fin H.n × Fin q, (enum a).val = s(Sum.inr v, Sum.inr w) then 2 / (d : ℚ) else 0) = _
        rw [if_pos ((hcore_iff a).mp hc)]
      rw [hlen]
      exact ⟨by positivity, by positivity⟩
    · simp only [hc, ↓reduceIte]
      have hbuy : D.buying a = 1 := by
        change (if ∃ v w : Fin H.n × Fin q, (enum a).val = s(Sum.inr v, Sum.inr w) then (0 : ℚ) else 1) = _
        rw [if_neg (mt (hcore_iff a).mpr hc)]
      rw [hbuy]
      exact ⟨by norm_num, by positivity⟩
  have hbuy_le : ∀ a, D.buying a ≤ Dpos.buying a := by
    intro a
    change D.buying a ≤ if coreResource H q d π hd a then 1 / (requests H : ℚ) else D.buying a
    by_cases hc : coreResource H q d π hd a
    · rw [if_pos hc]
      have : D.buying a = 0 := by
        change (if ∃ v w : Fin H.n × Fin q, (enum a).val = s(Sum.inr v, Sum.inr w) then (0 : ℚ) else 1) = 0
        rw [if_pos ((hcore_iff a).mp hc)]
      rw [this]
      positivity
    · rw [if_neg hc]
  have hlen_le : ∀ a, D.length a ≤ Dpos.length a := by
    intro a
    change D.length a ≤ if coreResource H q d π hd a then D.length a else 1 / (requests H : ℚ)
    by_cases hc : coreResource H q d π hd a
    · rw [if_pos hc]
    · rw [if_neg hc]
      have : D.length a = 0 := by
        change (if ∃ v w : Fin H.n × Fin q, (enum a).val = s(Sum.inr v, Sum.inr w) then 2 / (d : ℚ) else 0) = 0
        rw [if_neg (mt (hcore_iff a).mpr hc)]
      rw [this]
      positivity
  refine ⟨hbuy_pos, ?_, ?_, ?_⟩
  · exact ProofB.positiveFractionalWitness H q d g π hd hq base
  · intro r
    let s : D.toInstance.IntegralRouting := ⟨r.path, r.allowed_path⟩
    refine ⟨s, ?_⟩
    unfold integralObjective BuyAtBulk.Instance.integralBuyingCost BuyAtBulk.Instance.integralRentalCost
      BuyAtBulk.Instance.pathLength
    have h1 : ∑ a ∈ D.toInstance.usedResources s, D.buying a ≤
        ∑ a ∈ Dpos.toInstance.usedResources r, Dpos.buying a :=
      Finset.sum_le_sum fun a _ => hbuy_le a
    have h2 : ∑ i, D.demand i * (∑ a ∈ D.toInstance.uses (s.path i), D.length a) ≤
        ∑ i, Dpos.demand i * (∑ a ∈ Dpos.toInstance.uses (r.path i), Dpos.length a) := by
      refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun a _ => hlen_le a) (le_of_lt (D.demand_pos i))
    exact add_le_add h1 h2
  · intro f hf
    let f₀ : D.toInstance.FractionalSolution := ⟨f.opening, f.flow⟩
    have hf₀ : D.toInstance.Feasible f₀ := hf
    refine ⟨f₀, hf₀, ?_⟩
    unfold lpObjective BuyAtBulk.Instance.buyingCost BuyAtBulk.Instance.rentalCost
      BuyAtBulk.Instance.fractionalLength BuyAtBulk.Instance.pathLength
    have h1 : ∑ a, D.buying a * f₀.opening a ≤ ∑ a, Dpos.buying a * f.opening a :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hbuy_le a) (hf.1 a).1
    have h2 : ∑ i, D.demand i * (∑ p, (∑ a ∈ D.toInstance.uses p, D.length a) * f₀.flow i p) ≤
        ∑ i, Dpos.demand i * (∑ p, (∑ a ∈ Dpos.toInstance.uses p, Dpos.length a) * f.flow i p) := by
      refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_right
          (Finset.sum_le_sum fun a _ => hlen_le a) (hf.2.1 i p)) (le_of_lt (D.demand_pos i))
    exact add_le_add h1 h2

end BuyAtBulk.EdgeOnlyGap
