import BuyAtBulk.Model.CompactFlowPath

/-! Positive directed paths follow from finite nonnegative flow conservation;
no reachability or path-decomposition certificate is assumed. -/
noncomputable section
namespace BuyAtBulk.CompactFlow
variable {V : Type} [Fintype V] {G : SimpleGraph V}
local instance compactFlowReachabilityDecEq : DecidableEq V := Classical.decEq _
local instance compactFlowReachabilityDecRel : DecidableRel G.Adj := Classical.decRel _

/-- An oriented walk uses only strictly positive directed transport entries. -/
def PositiveWalk (f : V → V → ℚ) {s t : V} (p : G.Walk s t) : Prop :=
  ∀ d ∈ p.darts, 0 < f d.fst d.snd

theorem positive_path_of_balance (f : V → V → ℚ) (s t : V) (mass : ℚ)
    (mass_pos : 0 < mass) (nonneg : ∀ u v, 0 ≤ f u v)
    (nonedge : ∀ u v, ¬G.Adj u v → f u v = 0)
    (balance : ∀ v, (∑ u, f v u) - (∑ u, f u v) =
      mass * ((if s = v then 1 else 0) - (if t = v then 1 else 0))) :
    ∃ p : G.Path s t, PositiveWalk f p.val := by
  classical
  let reach : V → Prop := fun v => ∃ p : G.Walk s v, PositiveWalk f p
  have rs : reach s := ⟨.nil, by simp [PositiveWalk]⟩
  have closed : ∀ u v, reach u → 0 < f u v → reach v := by
    intro u v ⟨p, hp⟩ huv
    have adj : G.Adj u v := by
      by_contra hn
      have hzero := nonedge u v hn
      exact (ne_of_gt huv) hzero
    refine ⟨p.append adj.toWalk, ?_⟩
    intro d hd
    simp only [SimpleGraph.Walk.darts_append, SimpleGraph.Walk.darts_cons,
      SimpleGraph.Walk.darts_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hd
    rcases hd with hd | rfl
    · exact hp d hd
    · exact huv
  have rt : reach t := by
    by_contra hnt
    let S := Finset.univ.filter reach
    have hs : s ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rs⟩
    have ht : t ∉ S := by simpa [S] using hnt
    have row : ∀ u ∈ S, ∑ v, f u v = ∑ v ∈ S, f u v := by
      intro u hu
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro v _ hv
      apply le_antisymm _ (nonneg u v)
      by_contra h
      have pos : 0 < f u v := lt_of_not_ge h
      exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        closed u v (Finset.mem_filter.mp hu).2 pos⟩)
    have hout : (∑ u ∈ S, ∑ v, f u v) ≤ ∑ v ∈ S, ∑ u, f u v := by
      calc
        (∑ u ∈ S, ∑ v, f u v) = ∑ u ∈ S, ∑ v ∈ S, f u v :=
          Finset.sum_congr rfl row
        _ = ∑ v ∈ S, ∑ u ∈ S, f u v := Finset.sum_comm
        _ ≤ _ := ?_
      apply Finset.sum_le_sum
      intro v _
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => nonneg _ _)
    have hmass : (∑ v ∈ S, ((∑ u, f v u) - (∑ u, f u v))) = mass := by
      simp_rw [balance]
      rw [← Finset.mul_sum]
      simp [Finset.sum_sub_distrib, hs, ht]
    rw [Finset.sum_sub_distrib] at hmass
    linarith
  obtain ⟨p, hp⟩ := rt
  refine ⟨p.toPath, ?_⟩
  intro d hd
  exact hp d (p.darts_toPath_subset_darts hd)

end BuyAtBulk.CompactFlow
