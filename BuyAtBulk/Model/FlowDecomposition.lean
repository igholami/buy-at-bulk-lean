import BuyAtBulk.Model.NaturalLP
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! Rational Carathéodory compression of an explicitly finite path flow. This
is a sparse-support existence theorem, not a polynomial-time compact-LP solver. -/
namespace BuyAtBulk.FlowDecomposition

/-- A probability distribution on finitely many feature vectors has a rational
replacement on at most dimension+1 of its original positive-weight indices. -/
theorem sparse_weights {P : Type} [Fintype P] (n : ℕ)
    (v : P → Fin n → ℚ) (w : P → ℚ)
    (hw : ∀ p, 0 ≤ w p) (hs : ∑ p, w p = 1) :
    ∃ z : P → ℚ, (∀ p, 0 ≤ z p) ∧ (∑ p, z p = 1) ∧
      (∀ p, z p ≠ 0 → w p ≠ 0) ∧
      (Finset.univ.filter (fun p => z p ≠ 0)).card ≤ n + 1 ∧
      ∑ p, z p • v p = ∑ p, w p • v p := by
  classical
  let s := Finset.univ.filter fun p => w p ≠ 0
  let x := ∑ p, w p • v p
  have hsum : ∑ p ∈ s, w p = 1 := by simpa only [s, Finset.sum_filter_ne_zero] using hs
  have hx : x ∈ convexHull ℚ (v '' (s : Set P)) := by
    rw [_root_.convexHull_eq]
    refine ⟨P, s, w, v, (fun p _ => hw p), hsum, ?_, ?_⟩
    · intro p hp; exact ⟨p, hp, rfl⟩
    · rw [Finset.centerMass_eq_of_sum_1 _ _ hsum]
      simp only [s, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : w p = 0 <;> simp [hp]
  let t := Caratheodory.minCardFinsetOfMemConvexHull hx
  have ht := Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
  have ha := Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
  have hc : t.card ≤ n + 1 := by
    have h := ha.card_le_finrank_succ
    have hd := Submodule.finrank_le (vectorSpan ℚ (Set.range ((↑) : t → Fin n → ℚ)))
    have hd' : Module.finrank ℚ (vectorSpan ℚ (Set.range ((↑) : t → Fin n → ℚ))) ≤ n := by
      simpa using hd
    exact (by simpa [t] using h : t.card ≤ _).trans (Nat.add_le_add_right hd' 1)
  obtain ⟨a, ha0, hasum, hax⟩ := Finset.mem_convexHull'.mp
    (Caratheodory.mem_minCardFinsetOfMemConvexHull hx)
  have reps : ∀ y : t, ∃ p, p ∈ s ∧ v p = (y : Fin n → ℚ) := by
    intro y; exact ht y.property
  choose rep hrep using reps
  let z : P → ℚ := fun p => ∑ y : t, if rep y = p then a y else 0
  have hzsum : ∑ p, z p = ∑ y : t, a y := by
    simp only [z]
    rw [Finset.sum_comm]
    simp
  refine ⟨z, ?_, ?_, ?_, ?_, ?_⟩
  · intro p; exact Finset.sum_nonneg fun y _ => by
      split_ifs
      · exact ha0 y y.property
      · exact le_rfl
  · rw [hzsum]; simpa only [Finset.univ_eq_attach, Finset.sum_attach, t] using hasum
  · intro p hp
    by_contra hzero
    apply hp
    apply Finset.sum_eq_zero
    intro y _
    have hne : rep y ≠ p := by
      intro he; have := (Finset.mem_filter.mp (hrep y).1).2; exact this (he ▸ hzero)
    simp [hne]
  · have hsub : Finset.univ.filter (fun p => z p ≠ 0) ⊆
        Finset.univ.image rep := by
      intro p hp
      by_contra hn
      have hn' : ∀ y : t, rep y ≠ p := by simpa using hn
      have hz : z p = 0 := by simp [z, hn']
      exact (Finset.mem_filter.mp hp).2 hz
    exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (by simpa using hc))
  · calc
      ∑ p, z p • v p = ∑ y : t, a y • v (rep y) := by
        simp only [z, Finset.sum_smul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y _
        simp [ite_smul]
      _ = ∑ y : t, a y • (y : Fin n → ℚ) := by
        apply Finset.sum_congr rfl; intro y _; rw [(hrep y).2]
      _ = x := by
        change (∑ y ∈ t.attach, (fun e : Fin n → ℚ => a e • e) ↑y) = x
        rw [Finset.sum_attach (f := fun e : Fin n → ℚ => a e • e)]
        exact hax

end BuyAtBulk.FlowDecomposition
