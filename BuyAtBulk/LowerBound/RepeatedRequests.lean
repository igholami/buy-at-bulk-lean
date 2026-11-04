import BuyAtBulk.LowerBound.RequestCount
import Mathlib.Data.Fintype.EquivFin

namespace BuyAtBulk.LowerBound

/-- Pad a nonempty collection of `k`-subset requests to exactly `h` occurrences
by repeating a request. Every original request remains represented. -/
theorem exists_request_surjection (k h : ℕ) (hk : 1 ≤ k)
    (hh : requestCount k ≤ h) :
    ∃ request : Fin h → Request k, Function.Surjective request := by
  classical
  have hcard : Fintype.card (Request k) ≤ h := by rw [request_card]; exact hh
  have hpos : 0 < Fintype.card (Request k) := by
    rw [request_card]
    have := requestCount_lower k hk
    omega
  let e := Fintype.equivFin (Request k)
  let A₀ : Request k := e.symm ⟨0, hpos⟩
  let request : Fin h → Request k := fun i =>
    if hi : i.val < Fintype.card (Request k) then e.symm ⟨i.val, hi⟩ else A₀
  refine ⟨request, ?_⟩
  intro A
  let i : Fin h := ⟨(e A).val, lt_of_lt_of_le (e A).isLt hcard⟩
  refine ⟨i, ?_⟩
  change (if hi : (e A).val < Fintype.card (Request k) then
    e.symm ⟨(e A).val, hi⟩ else A₀) = A
  rw [dite_eq_left (e A).isLt]
  exact e.symm_apply_apply A

/-- Repetition preserves the integral feasible bought sets exactly. -/
theorem repeated_connectivity_iff (k h : ℕ) (request : Fin h → Request k)
    (hsurj : Function.Surjective request) (C : Finset (Ground k)) :
    (∀ i : Fin h, ∃ p : (graph k).Walk .root (.terminal (request i)),
      ∀ j, Vertex.paid j ∈ p.support → j ∈ C) ↔ NetworkFeasible k C := by
  constructor
  · intro h A
    obtain ⟨i, rfl⟩ := hsurj A
    exact h i
  · intro h i
    exact h (request i)

end BuyAtBulk.LowerBound
