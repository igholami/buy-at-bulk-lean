import BuyAtBulk.Model.CompactFlowBottleneck

/-! Finite rational path extraction from a compact commodity flow. Each
nonterminal extraction removes a positive directed arc; residual circulations
are discarded, so path resource use can decrease. -/
noncomputable section
namespace BuyAtBulk.CompactFlow
variable {V : Type} [Fintype V] {G : SimpleGraph V}
local instance compactFlowDecompositionDecEq : DecidableEq V := Classical.decEq _
local instance compactFlowDecompositionDecRel : DecidableRel G.Adj := Classical.decRel _

def pathSupport {s t : V} (w : G.Path s t → ℚ) : Finset (G.Path s t) :=
  Finset.univ.filter fun p => w p ≠ 0

private theorem decompose_aux (k : ℕ) :
    ∀ (f : V → V → ℚ) (s t : V) (mass : ℚ),
      (positiveArcs f).card = k → 0 ≤ mass →
      (∀ u v, 0 ≤ f u v) →
      (∀ u v, ¬G.Adj u v → f u v = 0) →
      (∀ v, (∑ u, f v u) - (∑ u, f u v) =
        mass * ((if s = v then 1 else 0) - (if t = v then 1 else 0))) →
      ∃ w : G.Path s t → ℚ, (∀ p, 0 ≤ w p) ∧ (∑ p, w p = mass) ∧
        (∀ u v, (∑ p, w p * transportVisits p.val u v) ≤ f u v) ∧
        (pathSupport w).card ≤ k + 1 := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro f s t mass hcard hmass hnonneg hnonedge balance
    by_cases hm : mass = 0
    · refine ⟨fun _ => 0, (fun _ => le_rfl), by simp [hm], ?_, ?_⟩
      · intro u v; simpa using hnonneg u v
      · simp [pathSupport]
    have masspos : 0 < mass := lt_of_le_of_ne hmass (Ne.symm hm)
    obtain ⟨P, hP⟩ := positive_path_of_balance f s t mass masspos hnonneg hnonedge balance
    obtain ⟨δ, δpos, δle, residual_nonneg, δstrict⟩ :=
      path_bottleneck P f hP hnonneg hnonedge mass masspos
    let residual : V → V → ℚ := fun u v => f u v - δ * transportVisits P.val u v
    have remainder : ∃ w : G.Path s t → ℚ, (∀ p, 0 ≤ w p) ∧
        (∑ p, w p = mass - δ) ∧
        (∀ u v, (∑ p, w p * transportVisits p.val u v) ≤ residual u v) ∧
        (pathSupport w).card ≤ k := by
      by_cases hd : δ = mass
      · refine ⟨fun _ => 0, (fun _ => le_rfl), by simp [hd], ?_, ?_⟩
        · intro u v; simpa [residual] using residual_nonneg u v
        · simp [pathSupport]
      · have hlt : (positiveArcs residual).card < k := by
          rw [← hcard]; exact δstrict (lt_of_le_of_ne δle hd)
        have residual_nonedge : ∀ u v, ¬G.Adj u v → residual u v = 0 := by
          intro u v hnv
          simp [residual, hnonedge u v hnv, transportVisits_nonedge _ u v hnv]
        obtain ⟨w, hw, hsum, hcap, hsize⟩ :=
          ih (positiveArcs residual).card hlt residual s t (mass - δ) rfl
            (sub_nonneg.mpr δle) residual_nonneg residual_nonedge
            (subtract_path_balance P f mass δ balance)
        exact ⟨w, hw, hsum, hcap, hsize.trans (by omega)⟩
    obtain ⟨w, hw, hsum, hcap, hsize⟩ := remainder
    let z : G.Path s t → ℚ := fun p => w p + if p = P then δ else 0
    have zsum : ∑ p, z p = mass := by
      simp only [z, Finset.sum_add_distrib]
      simp [hsum]
    refine ⟨z, (fun p => add_nonneg (hw p) (by split_ifs <;> positivity)), zsum, ?_, ?_⟩
    · intro u v
      have hsumuv : (∑ p, z p * transportVisits p.val u v) =
          (∑ p, w p * transportVisits p.val u v) + δ * transportVisits P.val u v := by
        simp only [z, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
        simp
      rw [hsumuv]
      have hc := hcap u v
      dsimp [residual] at hc
      linarith
    · have hsub : pathSupport z ⊆ insert P (pathSupport w) := by
        intro p hp
        by_cases he : p = P
        · exact Finset.mem_insert.mpr (Or.inl he)
        · apply Finset.mem_insert_of_mem
          simpa [pathSupport, z, he] using hp
      exact (Finset.card_le_card hsub).trans
        ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right hsize 1))

/-- Rational source/sink flow decomposes into finitely many positive weighted
simple paths, dominated arcwise by the input. At most one final path is added
after the strict arc-support elimination steps. -/
theorem decompose_transport (f : V → V → ℚ) (s t : V) (mass : ℚ)
    (hmass : 0 ≤ mass) (nonneg : ∀ u v, 0 ≤ f u v)
    (nonedge : ∀ u v, ¬G.Adj u v → f u v = 0)
    (balance : ∀ v, (∑ u, f v u) - (∑ u, f u v) =
      mass * ((if s = v then 1 else 0) - (if t = v then 1 else 0))) :
    ∃ w : G.Path s t → ℚ, (∀ p, 0 ≤ w p) ∧ (∑ p, w p = mass) ∧
      (∀ u v, (∑ p, w p * transportVisits p.val u v) ≤ f u v) ∧
      (pathSupport w).card ≤ (positiveArcs f).card + 1 :=
  decompose_aux (positiveArcs f).card f s t mass rfl hmass nonneg nonedge balance

end BuyAtBulk.CompactFlow
