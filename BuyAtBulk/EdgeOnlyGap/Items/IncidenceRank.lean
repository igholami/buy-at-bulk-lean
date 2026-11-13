import Mathlib.LinearAlgebra.Dimension.Finrank
import BuyAtBulk.EdgeOnlyGap.Items.Boundary
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofAGradientKernel
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofAComponentCount
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit incidence-rank formula, p. 4: binary columns on core vertices. -/
theorem incidenceRank (H : FiniteGraph) (W : Finset (Edges H)) :
  Module.finrank (ZMod 2) (LinearMap.range (boundary H W)) =
    (edgeSupport H W).card - edgeComponents H W := by
  classical
  let M : Matrix {e // e ∈ W} (Fin H.n) (ZMod 2) :=
    fun e v => if v = e.val.val.1 ∨ v = e.val.val.2 then 1 else 0
  have hm (e : {e // e ∈ W}) (v : Fin H.n) :
      M e v = (if v = e.val.val.1 then 1 else 0) +
        (if v = e.val.val.2 then 1 else 0) := by
    have hne := ne_of_lt e.val.prop.1
    by_cases h1 : v = e.val.val.1 <;> by_cases h2 : v = e.val.val.2 <;>
      simp_all [M]
  have hg : M.mulVecLin = ProofA.gradient H W := by
    apply LinearMap.ext
    intro x
    funext e
    change (∑ v, M e v * x v) = x e.val.val.1 + x e.val.val.2
    simp_rw [hm, add_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_add_distrib]
    simp
  have hb : M.transpose.mulVecLin = boundary H W := by
    apply LinearMap.ext
    intro x
    funext v
    change (∑ e, M e v * x e) = ∑ e, if v = e.val.val.1 ∨ v = e.val.val.2 then x e else 0
    apply Finset.sum_congr rfl
    intro e _
    simp only [M, ite_mul, one_mul, zero_mul]
  have hrank : Module.finrank (ZMod 2) (LinearMap.range (boundary H W)) =
      Module.finrank (ZMod 2) (LinearMap.range (ProofA.gradient H W)) := by
    rw [← hb, ← hg]
    exact Matrix.rank_transpose M
  have hk : Module.finrank (ZMod 2) (LinearMap.ker (ProofA.gradient H W)) =
      Nat.card (edgeSubgraph H W).ConnectedComponent := by
    rw [← (ProofA.gradientKernelEquiv H W).finrank_eq]
    letI := Fintype.ofFinite (edgeSubgraph H W).ConnectedComponent
    simp only [Module.finrank_pi, Nat.card_eq_fintype_card]
  have h := LinearMap.finrank_range_add_finrank_ker (ProofA.gradient H W)
  rw [hk, ProofA.componentCount H W] at h
  have hn : Module.finrank (ZMod 2) (Fin H.n → ZMod 2) = H.n := by
    simp only [Module.finrank_pi, Fintype.card_fin]
  rw [hn] at h
  have hs : (edgeSupport H W).card ≤ H.n := by
    simpa using Finset.card_le_univ (edgeSupport H W)
  rw [hrank]
  omega


end BuyAtBulk.EdgeOnlyGap
