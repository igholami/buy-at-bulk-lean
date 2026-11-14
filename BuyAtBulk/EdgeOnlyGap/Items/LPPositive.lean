import BuyAtBulk.EdgeOnlyGap.Items.Optima
import BuyAtBulk.EdgeOnlyGap.Items.SupplyData
import BuyAtBulk.EdgeOnlyGap.Items.RegularBase
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofCCoreCrossing

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit positivity bridge, pp. 1, 3, 5: each hub-to-hub route crosses a core edge. -/
theorem lpPositive (H : FiniteGraph) (q d g : ℕ) (π : Lift H q) (hd : 0 < d)
    (base : RegularBase H d g) (f : (supplyData H q d π hd).toInstance.FractionalSolution)
    (hf : (supplyData H q d π hd).toInstance.Feasible f) :
  (H.n:ℚ) ≤ lpObjective (supplyData H q d π hd).toInstance f ∧
    0 < lpObjective (supplyData H q d π hd).toInstance f := by
  classical
  have hdq : (0:ℚ) < d := by exact_mod_cast hd
  have key : ∀ t : (supplyData H q d π hd).TaggedPath, 2 / (d:ℚ) ≤ ∑ a ∈ (supplyData H q d π hd).pathResources t, (supplyData H q d π hd).length a := by
    rintro ⟨i, P⟩
    have hlt := ((Fintype.equivFin (Edges H)).symm i).property.1
    obtain ⟨x, y, hxy⟩ := proofC_coreCrossing H q π P.val
      ((Fintype.equivFin (Edges H)).symm i).val.1 ((Fintype.equivFin (Edges H)).symm i).val.2
      rfl rfl hlt.ne P.property
    have he : s(Sum.inr x, Sum.inr y) ∈ (supplyGraph H q π).edgeSet :=
      P.val.edges_subset_edgeSet hxy
    set a0 : Fin (supplyData H q d π hd).resourceCount := Fintype.equivFin (supplyGraph H q π).edgeSet ⟨_, he⟩ with ha0
    have hloc : (supplyData H q d π hd).location a0 = Sum.inr s(Sum.inr x, Sum.inr y) := by
      change Sum.inr ((Fintype.equivFin (supplyGraph H q π).edgeSet).symm a0).val = _
      rw [ha0, Equiv.symm_apply_apply]; rfl
    have hlen0 : (supplyData H q d π hd).length a0 = 2 / (d:ℚ) := by
      change (if ∃ v w : Fin H.n × Fin q,
        ((Fintype.equivFin (supplyGraph H q π).edgeSet).symm a0).val = s(Sum.inr v, Sum.inr w)
        then 2 / (d : ℚ) else 0) = _
      rw [ha0, Equiv.symm_apply_apply, if_pos ⟨x, y, rfl⟩]
    have hmem : a0 ∈ (supplyData H q d π hd).pathResources ⟨i, P⟩ := by
      simp only [GraphData.pathResources, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hloc]
      exact hxy
    rw [← hlen0]
    exact Finset.single_le_sum (fun a _ => (supplyData H q d π hd).length_nonneg a) hmem
  have hlen : ∀ p : Fin (supplyData H q d π hd).toInstance.pathCount, 2 / (d:ℚ) ≤ (supplyData H q d π hd).toInstance.pathLength p := fun p => key ((supplyData H q d π hd).decode p)
  have hhand := proofC_requestsHandshake H d g base
  have hhandq : 2 * (requests H : ℚ) = H.n * d := by exact_mod_cast hhand
  have hbuy : 0 ≤ (supplyData H q d π hd).toInstance.buyingCost f :=
    Finset.sum_nonneg fun a _ =>
      mul_nonneg ((supplyData H q d π hd).buying_nonneg a) (hf.1 a).1
  have hinner : ∀ i, 2 / (d:ℚ) ≤ (supplyData H q d π hd).toInstance.fractionalLength f i := by
    intro i
    calc 2 / (d:ℚ) = ∑ p, 2 / (d:ℚ) * f.flow i p := by
            rw [← Finset.mul_sum, hf.2.2.2.1 i, mul_one]
      _ ≤ _ := Finset.sum_le_sum fun p _ =>
            mul_le_mul_of_nonneg_right (hlen p) (hf.2.1 i p)
  have hrent : (H.n : ℚ) ≤ (supplyData H q d π hd).toInstance.rentalCost f := by
    calc (H.n : ℚ) = ∑ _i : Fin (requests H), 2 / (d:ℚ) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp
            linarith
      _ ≤ ∑ i : Fin (requests H), 1 * (supplyData H q d π hd).toInstance.fractionalLength f i :=
            Finset.sum_le_sum fun i _ => by rw [one_mul]; exact hinner i
      _ = _ := rfl
  have hnpos : (0:ℚ) < H.n := by exact_mod_cast base.1
  unfold lpObjective
  constructor <;> linarith
end BuyAtBulk.EdgeOnlyGap
