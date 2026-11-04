import BuyAtBulk.Model.CompactFlowReachability

/-! Every positive directed path admits a positive rational bottleneck.
Subtracting it leaves nonnegative arc flows and preserves divergence; unless
all remaining commodity mass is removed, a previously positive arc vanishes. -/
noncomputable section
namespace BuyAtBulk.CompactFlow
variable {V : Type} [Fintype V] {G : SimpleGraph V}
local instance compactFlowBottleneckDecEq : DecidableEq V := Classical.decEq _
local instance compactFlowBottleneckDecRel : DecidableRel G.Adj := Classical.decRel _

omit [Fintype V] in
theorem transportVisits_dart {s t : V} (p : G.Walk s t) (d : G.Dart) :
    transportVisits p d.fst d.snd = (p.darts.count d : ℚ) := by
  induction p with
  | nil => simp [transportVisits]
  | @cons u v t hadj p ih =>
    simp only [transportVisits, SimpleGraph.Walk.darts_cons, List.count_cons,
      Nat.cast_add, ih, beq_iff_eq, SimpleGraph.Dart.ext_iff, Prod.ext_iff]
    rw [add_comm]
    congr 1
    split_ifs <;> norm_num

omit [Fintype V] in
theorem path_transportVisits_dart {s t : V} (p : G.Path s t) (d : G.Dart) :
    transportVisits p.val d.fst d.snd = if d ∈ p.val.darts then 1 else 0 := by
  rw [transportVisits_dart]
  by_cases hd : d ∈ p.val.darts
  · have hc := List.count_eq_one_of_mem
      (p.val.darts_nodup_of_support_nodup p.property.support_nodup) hd
    simp [hd, hc]
  · simp [hd, List.count_eq_zero.mpr hd]

/-- The positive directed-arc support, indexed by ordered original vertices. -/
def positiveArcs (f : V → V → ℚ) : Finset (V × V) :=
  Finset.univ.filter fun e => 0 < f e.1 e.2

theorem path_bottleneck {s t : V} (p : G.Path s t) (f : V → V → ℚ)
    (positive : PositiveWalk f p.val) (nonneg : ∀ u v, 0 ≤ f u v)
    (_nonedge : ∀ u v, ¬G.Adj u v → f u v = 0)
    (mass : ℚ) (hmass : 0 < mass) :
    ∃ δ : ℚ, 0 < δ ∧ δ ≤ mass ∧
      (∀ u v, 0 ≤ f u v - δ * transportVisits p.val u v) ∧
      (δ < mass →
        (positiveArcs (fun u v => f u v - δ * transportVisits p.val u v)).card <
          (positiveArcs f).card) := by
  classical
  let S := insert mass (p.val.darts.toFinset.image fun d => f d.fst d.snd)
  have Snonempty : S.Nonempty := ⟨mass, Finset.mem_insert_self _ _⟩
  let δ := S.min' Snonempty
  have δmem : δ ∈ S := Finset.min'_mem S Snonempty
  have δpos : 0 < δ := by
    rcases Finset.mem_insert.mp δmem with hm | hmem
    · simpa [hm] using hmass
    · obtain ⟨d, hd, he⟩ := Finset.mem_image.mp hmem
      rw [← he]
      exact positive d (List.mem_toFinset.mp hd)
  have δmass : δ ≤ mass := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have δarc : ∀ d ∈ p.val.darts, δ ≤ f d.fst d.snd := by
    intro d hd
    apply Finset.min'_le
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨d, List.mem_toFinset.mpr hd, rfl⟩)
  have residual : ∀ u v, 0 ≤ f u v - δ * transportVisits p.val u v := by
    intro u v
    by_cases ha : G.Adj u v
    · let d : G.Dart := ⟨(u, v), ha⟩
      have hc := path_transportVisits_dart p d
      change transportVisits p.val u v = _ at hc
      rw [hc]
      by_cases hd : d ∈ p.val.darts
      · simpa [hd] using sub_nonneg.mpr (δarc d hd)
      · simp [hd, nonneg u v]
    · rw [transportVisits_nonedge _ u v ha, mul_zero, sub_zero]
      exact nonneg u v
  refine ⟨δ, δpos, δmass, residual, ?_⟩
  intro δlt
  have δne : δ ≠ mass := ne_of_lt δlt
  have hit : ∃ d ∈ p.val.darts, f d.fst d.snd = δ := by
    have hm : δ ∈ p.val.darts.toFinset.image (fun d => f d.fst d.snd) :=
      (Finset.mem_insert.mp δmem).resolve_left δne
    obtain ⟨d, hd, he⟩ := Finset.mem_image.mp hm
    exact ⟨d, List.mem_toFinset.mp hd, he⟩
  obtain ⟨d, hd, he⟩ := hit
  have support_subset : positiveArcs (fun u v => f u v - δ * transportVisits p.val u v) ⊆
      positiveArcs f := by
    intro e he'
    simp only [positiveArcs, Finset.mem_filter, Finset.mem_univ, true_and] at *
    have hn := mul_nonneg (le_of_lt δpos) (transportVisits_nonneg p.val e.1 e.2)
    linarith
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨support_subset, ?_⟩
  intro heq
  have hmem : (d.fst, d.snd) ∈ positiveArcs f := by
    simp only [positiveArcs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact positive d hd
  rw [← heq] at hmem
  have hcount := path_transportVisits_dart p d
  simp only [hd, ite_true] at hcount
  simp only [positiveArcs, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  rw [hcount, he] at hmem
  linarith

/-- Subtracting a weighted path preserves the source/sink divergence law. -/
theorem subtract_path_balance {s t : V} (p : G.Path s t)
    (f : V → V → ℚ) (mass δ : ℚ)
    (balance : ∀ v, (∑ u, f v u) - (∑ u, f u v) =
      mass * ((if s = v then 1 else 0) - (if t = v then 1 else 0))) :
    ∀ v, (∑ u, (f v u - δ * transportVisits p.val v u)) -
      (∑ u, (f u v - δ * transportVisits p.val u v)) =
      (mass - δ) * ((if s = v then 1 else 0) - (if t = v then 1 else 0)) := by
  intro v
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hi := visits_incoming p.val v
  have ho := visits_outgoing p.val v
  have hb := balance v
  have hh := congrArg (fun x : ℚ => δ * x) (hi.symm.trans ho)
  nlinarith only [hb, hh]

end BuyAtBulk.CompactFlow
