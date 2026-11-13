import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import BuyAtBulk.EdgeOnlyGap.Items.ConditionalMatching

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

private lemma card_subtype_mem_eq_sum {α β : Type*} [Fintype α] [DecidableEq β]
    (P : α → Prop) (f : α → β) (S T : Finset β)
    (hmaps : ∀ a : α, P a → f a ∈ S → f a ∈ S ∩ T) :
    (Fintype.card {a : α // P a ∧ f a ∈ S} : ℝ) =
      ∑ k ∈ S ∩ T, (Fintype.card {a : α // P a ∧ f a = k} : ℝ) := by
  classical
  have h1 : Fintype.card {a : α // P a ∧ f a ∈ S} =
      (Finset.univ.filter (fun a : α => P a ∧ f a ∈ S)).card :=
    Fintype.card_subtype _
  have h2 : ∀ k, Fintype.card {a : α // P a ∧ f a = k} =
      (Finset.univ.filter (fun a : α => P a ∧ f a = k)).card :=
    fun k => Fintype.card_subtype _
  have hfib : (Finset.univ.filter (fun a : α => P a ∧ f a ∈ S)).card =
      ∑ k ∈ S ∩ T, ((Finset.univ.filter (fun a : α => P a ∧ f a ∈ S)).filter (fun a => f a = k)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact hmaps a ha.1 ha.2
  have hfilter_eq : ∀ k ∈ S ∩ T,
      (Finset.univ.filter (fun a : α => P a ∧ f a ∈ S)).filter (fun a => f a = k) =
      Finset.univ.filter (fun a : α => P a ∧ f a = k) := by
    intro k hk
    have hkS : k ∈ S := (Finset.mem_inter.mp hk).1
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hP, _⟩, rfl⟩; exact ⟨hP, rfl⟩
    · rintro ⟨hP, rfl⟩; exact ⟨⟨hP, hkS⟩, rfl⟩
  rw [h1, hfib, Nat.cast_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [h2 k, hfilter_eq k hk]

private lemma cond_prob_mem_eq_sum {β : Type*} [DecidableEq β]
    (H : FiniteGraph) (q : ℕ) (E : Lift H q → Prop) (f : Lift H q → β)
    (S T : Finset β) (hmaps : ∀ π : Lift H q, E π → f π ∈ S → f π ∈ S ∩ T) :
    conditionalLiftProbability H q E (fun π => f π ∈ S) =
      ∑ k ∈ S ∩ T, conditionalLiftProbability H q E (fun π => f π = k) := by
  unfold conditionalLiftProbability liftProbability finiteProbability
  dsimp only
  have hc := card_subtype_mem_eq_sum E f S T hmaps
  simp only [← Nat.card_eq_fintype_card] at hc ⊢
  rw [hc, Finset.sum_div, Finset.sum_div]

/-- First part, p. 2: fresh query closes onto ≤T+1 old vertices with conditional probability ≤4T/q. -/
theorem surplusProbability (H : FiniteGraph) (q T : ℕ) (hist : List (Exposure H q))
    (e : Edges H) (old : Finset (Fin q)) (earlier : hist.length < T)
    (oldBound : old.card ≤ T+1) (hT : 4 ≤ T) (hq : 8*T ≤ q)
    (positive : 0 < liftProbability H q (exposureEvent H q hist)) :
  (∀ j, j ∉ exposedSources H q hist e →
    conditionalLiftProbability H q (exposureEvent H q hist) (fun π => π e j ∈ old) ≤ 4*T/(q:ℝ)) ∧
  (∀ k, k ∉ exposedTargets H q hist e →
    conditionalLiftProbability H q (exposureEvent H q hist) (fun π => (π e).symm k ∈ old) ≤ 4*T/(q:ℝ)) := by
  have hcm := conditionalMatching H q T hist earlier e positive
  rcases hcm with ⟨hcardT, hcardS, hprobF, hprobR⟩
  have hq_pos : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
  have hqmT_pos : (0 : ℝ) < (q - T : ℕ) := Nat.cast_pos.mpr (by omega)
  have h_arith : ((T + 1 : ℕ) : ℝ) / ((q - T : ℕ) : ℝ) ≤ 4 * (T : ℝ) / (q : ℝ) := by
    rw [div_le_div_iff₀ hqmT_pos hq_pos]
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub (by omega : T ≤ q)]
    have ht : (4 : ℝ) ≤ T := by exact_mod_cast hT
    have hqt : 8 * (T : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith
  constructor
  · intro j hj
    let avail := Finset.univ \ exposedTargets H q hist e
    have hmaps : ∀ π : Lift H q, exposureEvent H q hist π → π e j ∈ old → π e j ∈ old ∩ avail := by
      intro π hE hold
      rw [Finset.mem_inter]
      refine ⟨hold, ?_⟩
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hmem
      unfold exposedTargets at hmem
      simp only [List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq] at hmem
      rcases hmem with ⟨a, ⟨ha_hist, ha_e⟩, ha_t⟩
      have hπa : π a.1 a.2.1 = a.2.2 := hE a ha_hist
      rw [ha_e, ha_t] at hπa
      have hinj : a.2.1 = j := (π e).injective hπa
      apply hj
      unfold exposedSources
      simp only [List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
      exact ⟨a, ⟨ha_hist, ha_e⟩, hinj⟩
    rw [cond_prob_mem_eq_sum H q (exposureEvent H q hist) (fun π => π e j) old avail hmaps]
    have hsum_eq : (∑ k ∈ old ∩ avail,
        conditionalLiftProbability H q (exposureEvent H q hist) (fun π => π e j = k)) =
        ((old ∩ avail).card : ℝ) / (avail.card : ℝ) := by
      calc
        (∑ k ∈ old ∩ avail,
            conditionalLiftProbability H q (exposureEvent H q hist) (fun π => π e j = k))
          = ∑ _k ∈ old ∩ avail, (1 / (avail.card : ℝ)) := by
              refine Finset.sum_congr rfl fun k hk => ?_
              have hk_avail : k ∉ exposedTargets H q hist e :=
                (Finset.mem_sdiff.mp (Finset.mem_inter.mp hk).2).2
              exact hprobF j hj k hk_avail
        _ = ((old ∩ avail).card : ℝ) / (avail.card : ℝ) := by
              simp [div_eq_mul_inv]
    rw [hsum_eq]
    have havail_ge : ((q - T : ℕ) : ℝ) ≤ (avail.card : ℝ) := Nat.cast_le.mpr hcardT
    have hold_le : ((old ∩ avail).card : ℝ) ≤ ((T + 1 : ℕ) : ℝ) := by
      exact_mod_cast le_trans (Finset.card_le_card Finset.inter_subset_left) oldBound
    have h_step1 : ((old ∩ avail).card : ℝ) / (avail.card : ℝ) ≤ ((T + 1 : ℕ) : ℝ) / ((q - T : ℕ) : ℝ) :=
      div_le_div₀ (by positivity) hold_le hqmT_pos havail_ge
    exact le_trans h_step1 h_arith
  · intro k hk
    let avail := Finset.univ \ exposedSources H q hist e
    have hmaps : ∀ π : Lift H q, exposureEvent H q hist π → (π e).symm k ∈ old → (π e).symm k ∈ old ∩ avail := by
      intro π hE hold
      rw [Finset.mem_inter]
      refine ⟨hold, ?_⟩
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hmem
      unfold exposedSources at hmem
      simp only [List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq] at hmem
      rcases hmem with ⟨a, ⟨ha_hist, ha_e⟩, ha_s⟩
      have hπa : π a.1 a.2.1 = a.2.2 := hE a ha_hist
      rw [ha_e, ha_s, Equiv.apply_symm_apply] at hπa
      apply hk
      unfold exposedTargets
      simp only [List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
      exact ⟨a, ⟨ha_hist, ha_e⟩, hπa.symm⟩
    rw [cond_prob_mem_eq_sum H q (exposureEvent H q hist) (fun π => (π e).symm k) old avail hmaps]
    have hsum_eq : (∑ j ∈ old ∩ avail,
        conditionalLiftProbability H q (exposureEvent H q hist) (fun π => (π e).symm k = j)) =
        ((old ∩ avail).card : ℝ) / (avail.card : ℝ) := by
      calc
        (∑ j ∈ old ∩ avail,
            conditionalLiftProbability H q (exposureEvent H q hist) (fun π => (π e).symm k = j))
          = ∑ _j ∈ old ∩ avail, (1 / (avail.card : ℝ)) := by
              refine Finset.sum_congr rfl fun j hj => ?_
              have hj_avail : j ∉ exposedSources H q hist e :=
                (Finset.mem_sdiff.mp (Finset.mem_inter.mp hj).2).2
              exact hprobR k hk j hj_avail
        _ = ((old ∩ avail).card : ℝ) / (avail.card : ℝ) := by
              simp [div_eq_mul_inv]
    rw [hsum_eq]
    have havail_ge : ((q - T : ℕ) : ℝ) ≤ (avail.card : ℝ) := Nat.cast_le.mpr hcardS
    have hold_le : ((old ∩ avail).card : ℝ) ≤ ((T + 1 : ℕ) : ℝ) := by
      exact_mod_cast le_trans (Finset.card_le_card Finset.inter_subset_left) oldBound
    have h_step1 : ((old ∩ avail).card : ℝ) / (avail.card : ℝ) ≤ ((T + 1 : ℕ) : ℝ) / ((q - T : ℕ) : ℝ) :=
      div_le_div₀ (by positivity) hold_le hqmT_pos havail_ge
    exact le_trans h_step1 h_arith

end BuyAtBulk.EdgeOnlyGap
