import BuyAtBulk.LowerBound.Construction
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

namespace BuyAtBulk.LowerBound

/-- The hitting sets in the source lower-bound construction are precisely
those containing at least `k+1` paid nodes. -/
theorem hitsAll_iff (k : ℕ) (C : Finset (Ground k)) :
    HitsAll k C ↔ k < C.card := by
  classical
  constructor
  · intro h
    by_contra hn
    have hc : C.card ≤ k := by omega
    have hcomp : k ≤ Cᶜ.card := by
      simpa only [Finset.card_compl, Fintype.card_fin] using
        (show k ≤ 2 * k - C.card by omega)
    obtain ⟨A, hA, hcard⟩ := Finset.exists_subset_card_eq hcomp
    obtain ⟨j, hjA, hjC⟩ := h A hcard
    have := hA hjA
    simp [hjC] at this
  · intro hc A hcard
    by_contra hn
    have hsub : A ⊆ Cᶜ := by
      intro j hj
      simp only [Finset.mem_compl]
      intro hjC
      exact hn ⟨j, hj, hjC⟩
    have hle := Finset.card_le_card hsub
    simp only [Finset.card_compl, Fintype.card_fin, hcard] at hle
    have hbound : C.card ≤ 2 * k := by
      simpa using Finset.card_le_univ C
    omega

/-- The exact integral optimum of the covering construction. -/
theorem integral_optimum (k : ℕ) (hk : 1 ≤ k) :
    (∀ C : Finset (Ground k), HitsAll k C → k + 1 ≤ C.card) ∧
    ∃ C : Finset (Ground k), HitsAll k C ∧ C.card = k + 1 := by
  classical
  constructor
  · intro C hC
    exact (hitsAll_iff k C).mp hC
  · have hbound : k + 1 ≤ (Finset.univ : Finset (Ground k)).card := by
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨C, _, hC⟩ := Finset.exists_subset_card_eq hbound
    refine ⟨C, (hitsAll_iff k C).mpr ?_, hC⟩
    omega

end BuyAtBulk.LowerBound
