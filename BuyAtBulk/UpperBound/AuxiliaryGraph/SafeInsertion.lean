import BuyAtBulk.UpperBound.AuxiliaryGraph.Realizations

namespace BuyAtBulk.UpperBound.AuxiliaryGraph
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A genuinely new scale birth is isolated from every older edge at that
scale. Eligibility of old edge endpoints is supplied by the actual trace guard. -/
theorem birth_isolated {physical : V → ℚ} {Q : ℚ} (event : AuxiliaryEvent G)
    (guard : AuxiliaryGuard G physical Q event) {vertex : V} {prior : RoundingState G}
    (reason : event.birthReason = some (vertex, prior)) :
    ∀ w, ¬ (atScale event.before.edges event.edge.scale).Adj vertex w := by
  have born := guard.2.2.2.2.2
  rw [reason] at born
  obtain ⟨endpoint, oldedges, eligible, fresh⟩ := born
  intro w adjacent
  obtain ⟨⟨edge, member, scale, endpoints⟩, distinct⟩ := adjacent
  have priorMember : edge ∈ prior.edges := by rw [oldedges]; exact member
  obtain ⟨hsource, htarget⟩ := new_birth_has_no_old_incident G prior eligible vertex
    event.edge.scale fresh edge priorMember scale
  have hmem : vertex ∈ key edge := by rw [← endpoints]; simp
  rcases (Sym2.mem_iff.mp hmem) with heq | heq
  · exact hsource heq.symm
  · exact htarget heq.symm

private theorem no_walk_of_isolated {H : SimpleGraph V} {u v : V}
    (distinct : u ≠ v) (isolated : ∀ w, ¬ H.Adj u w) (walk : H.Walk u v) : False := by
  cases walk with
  | nil => exact distinct rfl
  | cons edge rest => exact isolated _ edge

/-- The source insertion tests rule out every short older auxiliary bypass.
Physical realizations and allowance order are used to derive this fact; it is
not a supplied girth or abstract expansion hypothesis. -/
theorem no_short_old_walk {physical : V → ℚ} (physical_nonneg : ∀ v, 0 ≤ physical v)
    {Q : ℚ} {r : ℕ} (hr : 1 ≤ r) (hQ : 6 * (r : ℚ) ≤ Q)
    (event : AuxiliaryEvent G) (guard : AuxiliaryGuard G physical Q event)
    (allowance_pos : 0 < event.allowance)
    (distinct : event.edge.source ≠ event.edge.target)
    (old : OldBounds physical event.before event.allowance)
    (walk : (atScale event.before.edges event.edge.scale).Walk event.edge.source event.edge.target)
    (short : walk.length + 1 ≤ 2 * r) : False := by
  have reasonGuard := guard.2.2.2.2.2
  cases reason : event.birthReason with
  | none =>
    rw [reason] at reasonGuard
    have nonempty : ¬ walk.Nil := SimpleGraph.Walk.not_nil_of_ne distinct
    obtain ⟨path, bought, weight⟩ := realize_walk physical_nonneg old walk nonempty
    apply reasonGuard
    refine ⟨path, bought, weight.trans ?_⟩
    have hlen : (walk.length : ℚ) + 1 ≤ 2 * (r : ℚ) := by exact_mod_cast short
    have hmul := mul_le_mul_of_nonneg_left (show (walk.length : ℚ) ≤ 2 * (r : ℚ) - 1 by linarith)
      (show 0 ≤ 3 * event.allowance by positivity)
    have hthreshold := mul_le_mul_of_nonneg_right hQ allowance_pos.le
    nlinarith
  | some born =>
    obtain ⟨vertex, prior⟩ := born
    rw [reason] at reasonGuard
    have isolated := birth_isolated event guard reason
    cases reasonGuard.1 with
    | inl hs =>
      subst vertex
      exact no_walk_of_isolated distinct isolated walk
    | inr ht =>
      subst vertex
      exact no_walk_of_isolated distinct.symm isolated walk.reverse

end BuyAtBulk.UpperBound.AuxiliaryGraph
