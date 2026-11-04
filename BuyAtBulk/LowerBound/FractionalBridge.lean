import BuyAtBulk.LowerBound.GraphLP
import BuyAtBulk.LowerBound.FractionalOptimum

namespace BuyAtBulk.LowerBound
open scoped BigOperators

/-- Every feasible path LP induces a feasible fractional cover, by the last
paid neighbor of each terminal. -/
theorem fractional_cover_of_feasible (k h : ℕ) (request : Fin h → Request k)
    (hsurj : Function.Surjective request)
    (f : (graphData k h request).toInstance.FractionalSolution)
    (hf : (graphData k h request).toInstance.Feasible f) :
    FractionalCover k (fun a => (f.opening a : ℝ)) := by
  classical
  let D := graphData k h request
  refine ⟨?_, ?_⟩
  · intro a
    constructor
    · change (0 : ℝ) ≤ (f.opening a : ℝ)
      exact_mod_cast (hf.1 a).1
    · change (f.opening a : ℝ) ≤ 1
      exact_mod_cast (hf.1 a).2
  · intro A hA
    obtain ⟨i, hi⟩ := hsurj ⟨A, hA⟩
    have hp_lower : ∀ p : Fin D.toInstance.pathCount,
        f.flow i p ≤ ∑ a ∈ A, if a ∈ D.toInstance.uses p then f.flow i p else 0 := by
      intro p
      by_cases hp : D.toInstance.allowed i p = true
      · obtain ⟨walk, _, huses⟩ := D.realization.path_sound i p hp
        have hit := walk_hits k (request i) walk
        obtain ⟨a, ha, hawalk⟩ := hit
        have haA : a ∈ A := by simpa [hi] using ha
        have hau : a ∈ D.toInstance.uses p := by
          rw [huses]
          change a ∈ Finset.univ.filter (fun j => Vertex.paid j ∈ walk.support)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hawalk⟩
        have hsingle := Finset.single_le_sum
          (fun j (_ : j ∈ A) => (show (0 : ℚ) ≤ if j ∈ D.toInstance.uses p then f.flow i p else 0 by
            split_ifs <;> first | exact hf.2.1 i p | exact le_rfl)) haA
        simpa [hau] using hsingle
      · have hpfalse : D.toInstance.allowed i p = false := by
          cases heq : D.toInstance.allowed i p <;> simp_all
        rw [hf.2.2.1 i p hpfalse]
        apply Finset.sum_nonneg
        intro a ha
        split_ifs <;> norm_num
    have hcover : (1 : ℚ) ≤ ∑ a ∈ A, f.opening a := calc
      1 = ∑ p, f.flow i p := (hf.2.2.2.1 i).symm
      _ ≤ ∑ p, ∑ a ∈ A, if a ∈ D.toInstance.uses p then f.flow i p else 0 :=
        Finset.sum_le_sum fun p hp => hp_lower p
      _ = ∑ a ∈ A, D.toInstance.resourceFlow f i a := by
        rw [Finset.sum_comm]
        rfl
      _ ≤ ∑ a ∈ A, f.opening a := Finset.sum_le_sum fun a ha => hf.2.2.2.2 i a
    change (1 : ℝ) ≤ ∑ a ∈ A, (f.opening a : ℝ)
    exact_mod_cast hcover

/-- Every natural graph LP solution costs at least two, so the uniform
solution realizes the source's exact fractional optimum, not only an upper
bound sufficient for an integrality-gap certificate. -/
theorem graph_fractional_buying_lower (k h : ℕ) (hk : 1 ≤ k)
    (request : Fin h → Request k) (hsurj : Function.Surjective request)
    (f : (graphData k h request).toInstance.FractionalSolution)
    (hf : (graphData k h request).toInstance.Feasible f) :
    (2 : ℚ) ≤ (graphData k h request).toInstance.buyingCost f := by
  have hcover := fractional_cover_of_feasible k h request hsurj f hf
  have hreal := (fractional_optimum k hk).1 _ hcover
  have hsum : (2 : ℚ) ≤ ∑ a, f.opening a := by exact_mod_cast hreal
  simpa [Instance.buyingCost, graphData, GraphData.toInstance] using hsum

end BuyAtBulk.LowerBound
