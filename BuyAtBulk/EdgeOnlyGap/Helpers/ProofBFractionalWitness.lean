import BuyAtBulk.EdgeOnlyGap.Items.FractionalWitness
import BuyAtBulk.EdgeOnlyGap.Items.RegularBase
import BuyAtBulk.EdgeOnlyGap.Items.Handshaking
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- The displayed fractional witness needs only positive degree and lift size. -/
theorem ProofB.fractionalWitnessCosts (H : FiniteGraph) (d g q : ℕ) (base : RegularBase H d g)
    (hd : 0 < d) (hq : 0 < q) (π : Lift H q) :
  let D := supplyData H q d π hd
  let f := fractionalWitness H q d π hd
  D.toInstance.Feasible f ∧ D.toInstance.buyingCost f = H.n ∧
    D.toInstance.rentalCost f = H.n ∧
    (∀ i a, D.toInstance.resourceFlow f i a ≤ 1 / (q : ℚ)) := by
  classical
  intro D f
  let G := supplyGraph H q π
  let enum : Fin D.resourceCount ≃ G.edgeSet := (Fintype.equivFin G.edgeSet).symm
  let req : Fin D.requestCount ≃ Edges H := (Fintype.equivFin (Edges H)).symm
  have hq_pos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hq_ne : (q : ℚ) ≠ 0 := ne_of_gt hq_pos
  have hd_pos : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  have hd_ne : (d : ℚ) ≠ 0 := ne_of_gt hd_pos
  have h1q_nonneg : (0 : ℚ) ≤ 1 / (q : ℚ) := by positivity
  have h1q_le_one : 1 / (q : ℚ) ≤ 1 := by
    rw [div_le_iff₀ hq_pos, one_mul]
    exact_mod_cast hq
  have hflow_sum : ∀ i, ∑ p, f.flow i p = 1 := by
    intro i
    change ∑ p, (∑ j : Fin q, if p = D.encode i (witnessPath H q π (req i) j) then 1 / (q : ℚ) else 0) = 1
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one_div_cancel hq_ne]
  have hres_flow : ∀ i a, D.toInstance.resourceFlow f i a ≤ 1 / (q : ℚ) := by
    intro i a
    unfold BuyAtBulk.Instance.resourceFlow
    change ∑ p, (if a ∈ D.toInstance.uses p then
      (∑ j : Fin q, if p = D.encode i (witnessPath H q π (req i) j) then 1 / (q : ℚ) else 0) else 0) ≤ 1 / (q : ℚ)
    have hcomm : (∑ p, if a ∈ D.toInstance.uses p then
        (∑ j : Fin q, if p = D.encode i (witnessPath H q π (req i) j) then 1 / (q : ℚ) else 0) else 0) =
        ∑ j : Fin q, if a ∈ D.toInstance.uses (D.encode i (witnessPath H q π (req i) j)) then 1 / (q : ℚ) else 0 := by
      trans ∑ p, ∑ j : Fin q, if a ∈ D.toInstance.uses p ∧ p = D.encode i (witnessPath H q π (req i) j) then 1 / (q : ℚ) else 0
      · refine Finset.sum_congr rfl fun p _ => ?_
        by_cases ha : a ∈ D.toInstance.uses p <;> simp [ha]
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        have : ∀ p, (if a ∈ D.toInstance.uses p ∧ p = D.encode i (witnessPath H q π (req i) j) then 1 / (q : ℚ) else 0) =
            if p = D.encode i (witnessPath H q π (req i) j) then
              (if a ∈ D.toInstance.uses (D.encode i (witnessPath H q π (req i) j)) then 1 / (q : ℚ) else 0) else 0 := by
          intro p
          by_cases hp : p = D.encode i (witnessPath H q π (req i) j) <;> simp [hp]
        simp_rw [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hcomm]
    let S := Finset.univ.filter fun j : Fin q => a ∈ D.toInstance.uses (D.encode i (witnessPath H q π (req i) j))
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard_le : S.card ≤ 1 := by
      rw [Finset.card_le_one_iff]
      intro j₁ j₂ hj₁ hj₂
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj₁ hj₂
      erw [D.decode_encode] at hj₁ hj₂
      simp only [BuyAtBulk.GraphData.pathResources, Finset.mem_filter,
        Finset.mem_univ, true_and] at hj₁ hj₂
      change (enum a).val ∈ (witnessPath H q π (req i) j₁).val.edges at hj₁
      change (enum a).val ∈ (witnessPath H q π (req i) j₂).val.edges at hj₂
      dsimp [witnessPath] at hj₁ hj₂
      simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hj₁ hj₂
      have hne := ne_of_lt (req i).prop.1
      rcases hj₁ with h1 | h1 | h1 <;> rcases hj₂ with h2 | h2 | h2
      all_goals
        have heq := h1.symm.trans h2
        simp only [Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq,
          reduceCtorEq, hne, Ne.symm hne, true_and, and_true, false_and, and_false,
          false_or, or_false, eq_self_iff_true] at heq
      all_goals first | exact heq | exact heq.1 | exact (π (req i)).injective heq
    calc (S.card : ℚ) * (1 / (q : ℚ))
      _ ≤ 1 * (1 / (q : ℚ)) := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_le) h1q_nonneg
      _ = 1 / (q : ℚ) := one_mul _
  have hfeas : D.toInstance.Feasible f := by
    refine ⟨fun _ => ⟨h1q_nonneg, h1q_le_one⟩, fun i p => ?_, fun i p hallow => ?_, hflow_sum, hres_flow⟩
    · change 0 ≤ ∑ j : Fin q, if p = D.encode i (witnessPath H q π (req i) j) then 1 / (q : ℚ) else 0
      exact Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
    · change (∑ j : Fin q, if p = D.encode i (witnessPath H q π (req i) j) then 1 / (q : ℚ) else 0) = 0
      refine Finset.sum_eq_zero fun j _ => ?_
      split_ifs with hp
      · subst hp
        have := D.allowed_encode i (witnessPath H q π (req i) j)
        rw [this] at hallow
        exact Bool.noConfusion hallow
      · rfl
  have hbuy : D.toInstance.buyingCost f = H.n := by
    unfold BuyAtBulk.Instance.buyingCost
    change ∑ a, D.buying a * (1 / (q : ℚ)) = H.n
    rw [← Finset.sum_mul]
    let spokes := Finset.univ.filter fun a : Fin D.resourceCount =>
      ¬ ∃ v w : Fin H.n × Fin q, (enum a).val = s(Sum.inr v, Sum.inr w)
    have hsum_spokes : ∑ a, D.buying a = (spokes.card : ℚ) := by
      have : ∀ a : Fin D.resourceCount, D.buying a = if a ∈ spokes then 1 else 0 := by
        intro a
        simp only [spokes, Finset.mem_filter, Finset.mem_univ, true_and]
        change (if ∃ v w : Fin H.n × Fin q, (enum a).val = s(Sum.inr v, Sum.inr w) then (0 : ℚ) else 1) = _
        split_ifs <;> simp_all
      simp_rw [this, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hspokes_card : spokes.card = H.n * q := by
      let φ : Fin H.n × Fin q → G.edgeSet := fun ⟨v, j⟩ =>
        ⟨s(Sum.inl v, Sum.inr (v, j)), by
          change (supplyGraph H q π).Adj (Sum.inl v) (Sum.inr (v, j))
          dsimp [supplyGraph]
          rw [SimpleGraph.fromRel_adj]
          exact ⟨by simp, Or.inl (Or.inl ⟨v, j, rfl, rfl⟩)⟩⟩
      refine (Finset.card_bij (s := (Finset.univ : Finset (Fin H.n × Fin q))) (t := spokes) (fun (vj : Fin H.n × Fin q) _ => enum.symm (φ vj))
        (fun ⟨v, j⟩ _ => by
          simp only [spokes, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply]
          rintro ⟨v', w', heq⟩
          simp only [φ, Sym2.eq_iff] at heq
          rcases heq with ⟨hfalse, _⟩ | ⟨hfalse, _⟩ <;> cases hfalse)
        (fun ⟨v₁, j₁⟩ _ ⟨v₂, j₂⟩ _ heq => by
          have hφ := congrArg Subtype.val (enum.symm.injective heq)
          simp only [φ, Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq] at hφ
          rcases hφ with ⟨_, hj⟩ | ⟨hfalse, _⟩
          · exact hj
          · cases hfalse)
        (fun a ha => by
          simp only [spokes, Finset.mem_filter, Finset.mem_univ, true_and] at ha
          generalize he : (enum a).val = s
          have hs : s ∈ G.edgeSet := he ▸ (enum a).property
          induction s using Sym2.inductionOn with
          | hf x y =>
            change (supplyGraph H q π).Adj x y at hs
            dsimp [supplyGraph] at hs
            rw [SimpleGraph.fromRel_adj] at hs
            rcases hs.2 with (⟨v, j, rfl, rfl⟩ | ⟨v, w, rfl, rfl, _⟩) |
                             (⟨v, j, rfl, rfl⟩ | ⟨v, w, rfl, rfl, _⟩)
            · refine ⟨(v, j), Finset.mem_univ _, ?_⟩
              apply enum.injective
              rw [Equiv.apply_symm_apply]
              exact Subtype.ext he.symm
            · exact False.elim (ha ⟨v, w, he⟩)
            · refine ⟨(v, j), Finset.mem_univ _, ?_⟩
              apply enum.injective
              rw [Equiv.apply_symm_apply]
              exact Subtype.ext (Sym2.eq_swap.trans he.symm)
            · exact False.elim (ha ⟨w, v, he⟩))).symm.trans (by simp)
    rw [hsum_spokes, hspokes_card]
    push_cast
    field_simp [hq_ne]
  have hrent : D.toInstance.rentalCost f = H.n := by
    unfold BuyAtBulk.Instance.rentalCost
    have hdem : ∀ i, D.toInstance.demand i = 1 := fun _ => rfl
    change (∑ i : Fin D.toInstance.requestCount, 1 * D.toInstance.fractionalLength f i) = _
    simp only [one_mul]
    have hwp_len : ∀ i (j : Fin q), D.toInstance.pathLength (D.encode i (witnessPath H q π (req i) j)) = 2 / (d : ℚ) := by
      intro i j
      unfold BuyAtBulk.Instance.pathLength
      erw [D.uses_encode]
      let e := req i
      let s_core : Sym2 (SupplyVertex H q) := s(Sum.inr (e.val.1, j), Sum.inr (e.val.2, π e j))
      have hs_core : s_core ∈ G.edgeSet := by
        change (supplyGraph H q π).Adj (Sum.inr (e.val.1, j)) (Sum.inr (e.val.2, π e j))
        dsimp [supplyGraph, liftGraph]
        rw [SimpleGraph.fromRel_adj]
        have hne : (Sum.inr (e.val.1, j) : SupplyVertex H q) ≠ Sum.inr (e.val.2, π e j) :=
          fun h => ne_of_lt e.prop.1 (congrArg Prod.fst (Sum.inr.inj h))
        refine ⟨hne, Or.inl (Or.inr ⟨(e.val.1, j), (e.val.2, π e j), rfl, rfl, ?_⟩)⟩
        rw [SimpleGraph.fromRel_adj]
        exact ⟨fun h => ne_of_lt e.prop.1 (congrArg Prod.fst h), Or.inl ⟨e, rfl, rfl, rfl⟩⟩
      let a_core := enum.symm ⟨s_core, hs_core⟩
      have hterm : ∀ a ∈ D.pathResources ⟨i, witnessPath H q π e j⟩,
          D.toInstance.length a = if a = a_core then 2 / (d : ℚ) else 0 := by
        intro a ha
        simp only [BuyAtBulk.GraphData.pathResources, Finset.mem_filter, Finset.mem_univ, true_and] at ha
        change (enum a).val ∈ (witnessPath H q π e j).val.edges at ha
        dsimp [witnessPath] at ha
        simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_cons,
          List.not_mem_nil, or_false] at ha
        change (if ∃ v w : Fin H.n × Fin q, (enum a).val = s(Sum.inr v, Sum.inr w) then 2 / (d : ℚ) else 0) =
          if a = a_core then 2 / (d : ℚ) else 0
        rcases ha with h1 | h2 | h3
        · have hnot : ¬ ∃ v w : Fin H.n × Fin q, (enum a).val = s(Sum.inr v, Sum.inr w) := by
            rintro ⟨v, w, hvw⟩
            have heq := h1.symm.trans hvw
            simp only [Sym2.eq_iff] at heq
            rcases heq with ⟨hfalse, _⟩ | ⟨hfalse, _⟩ <;> cases hfalse
          have hne_core : a ≠ a_core := by
            rintro rfl
            exact hnot ⟨(e.val.1, j), (e.val.2, π e j), by simp [a_core, s_core]⟩
          rw [if_neg hnot, if_neg hne_core]
        · have hex : ∃ v w : Fin H.n × Fin q, (enum a).val = s(Sum.inr v, Sum.inr w) :=
            ⟨(e.val.1, j), (e.val.2, π e j), h2⟩
          have heq_core : a = a_core := by
            apply enum.injective
            rw [Equiv.apply_symm_apply]
            exact Subtype.ext h2
          rw [if_pos hex, if_pos heq_core]
        · have hnot : ¬ ∃ v w : Fin H.n × Fin q, (enum a).val = s(Sum.inr v, Sum.inr w) := by
            rintro ⟨v, w, hvw⟩
            have heq := h3.symm.trans hvw
            simp only [Sym2.eq_iff] at heq
            rcases heq with ⟨_, hfalse⟩ | ⟨_, hfalse⟩ <;> cases hfalse
          have hne_core : a ≠ a_core := by
            rintro rfl
            exact hnot ⟨(e.val.1, j), (e.val.2, π e j), by simp [a_core, s_core]⟩
          rw [if_neg hnot, if_neg hne_core]
      have hmem_core : a_core ∈ D.pathResources ⟨i, witnessPath H q π e j⟩ := by
        simp only [BuyAtBulk.GraphData.pathResources, Finset.mem_filter, Finset.mem_univ, true_and]
        change (enum a_core).val ∈ (witnessPath H q π e j).val.edges
        have : (enum a_core).val = s_core := by simp [a_core]
        rw [this]
        dsimp [witnessPath, s_core]
        simp
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq', if_pos hmem_core]
    have hflen : ∀ i, D.toInstance.fractionalLength f i = 2 / (d : ℚ) := by
      intro i
      unfold BuyAtBulk.Instance.fractionalLength
      change ∑ p, D.toInstance.pathLength p *
        (∑ j : Fin q, if p = D.encode i (witnessPath H q π (req i) j) then 1 / (q : ℚ) else 0) = 2 / (d : ℚ)
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      have h1 : ∀ j : Fin q, (∑ p, D.toInstance.pathLength p *
          (if p = D.encode i (witnessPath H q π (req i) j) then 1 / (q : ℚ) else 0)) =
          (2 / (d : ℚ)) * (1 / (q : ℚ)) := by
        intro j
        have : ∀ p, D.toInstance.pathLength p * (if p = D.encode i (witnessPath H q π (req i) j) then 1 / (q : ℚ) else 0) =
            if p = D.encode i (witnessPath H q π (req i) j) then D.toInstance.pathLength (D.encode i (witnessPath H q π (req i) j)) * (1 / (q : ℚ)) else 0 := by
          intro p
          split_ifs with hp <;> simp [hp]
        simp_rw [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hwp_len]
      simp_rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [hq_ne, hd_ne]
    simp_rw [hflen, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hhs : 2 * (D.toInstance.requestCount : ℚ) = (H.n : ℚ) * (d : ℚ) := by
      exact_mod_cast handshaking H d g base
    field_simp [hd_ne]
    linarith
  exact ⟨hfeas, hbuy, hrent, hres_flow⟩

end BuyAtBulk.EdgeOnlyGap
