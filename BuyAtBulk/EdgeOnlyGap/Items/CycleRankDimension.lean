import Mathlib.LinearAlgebra.Dimension.Finrank
import BuyAtBulk.EdgeOnlyGap.Items.CycleSpace
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofACycleNullity
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofAComponentConnected
import BuyAtBulk.EdgeOnlyGap.Items.ComponentEdgeCounts
import Mathlib.Algebra.BigOperators.Ring.Finset

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 2: beta is cycle-space dimension and additive on edge-containing components. -/
theorem cycleRankDimension (H : FiniteGraph) (W : Finset (Edges H)) :
  Module.finrank (ZMod 2) (cycleSpace H W) = beta H W ∧
  beta H W = ∑ c ∈ (edgeSupport H W).image (edgeSubgraph H W).connectedComponentMk,
    beta H (W.filter fun e => (edgeSubgraph H W).connectedComponentMk e.val.1 = c) ∧
  beta H ∅ = 0 := by
  classical
  refine ⟨ProofA.cycleNullity H W, ?_, ?_⟩
  · let comps := (edgeSupport H W).image (edgeSubgraph H W).connectedComponentMk
    let U (c : (edgeSubgraph H W).ConnectedComponent) :=
      W.filter fun e => (edgeSubgraph H W).connectedComponentMk e.val.1 = c
    have hconn : ∀ c ∈ comps, edgeComponents H (U c) = 1 := by
      intro c hc
      apply ProofA.componentConnected H W c
      rcases Finset.mem_image.mp hc with ⟨v, hv, rfl⟩
      rw [edgeSupport, Finset.mem_biUnion] at hv
      rcases hv with ⟨e, he, hv⟩
      refine ⟨e, Finset.mem_filter.mpr ⟨he, ?_⟩⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · rfl
      · apply SimpleGraph.ConnectedComponent.eq.mpr
        apply SimpleGraph.Adj.reachable
        rw [edgeSubgraph, SimpleGraph.fromRel_adj]
        exact ⟨ne_of_lt e.prop.1, Or.inl ⟨e, he, rfl, rfl⟩⟩
    have hs : (edgeSupport H W).card = ∑ c ∈ comps, (edgeSupport H (U c)).card := by
      simp only [U, ProofA.componentSupport]
      apply Finset.card_eq_sum_card_fiberwise
      intro v hv
      exact Finset.mem_image_of_mem _ hv
    have he := componentEdgeCounts H W
    change W.card = ∑ c ∈ comps, (U c).card at he
    apply Int.ofNat_injective
    change (beta H W : ℤ) = ((∑ c ∈ comps, beta H (U c) : ℕ) : ℤ)
    rw [(cycleRankFormula H W).2]
    have hb : ((∑ c ∈ comps, beta H (U c) : ℕ) : ℤ) =
        ∑ c ∈ comps, (((U c).card : ℤ) - (edgeSupport H (U c)).card + 1) := by
      push_cast
      apply Finset.sum_congr rfl
      intro c hc
      rw [(cycleRankFormula H (U c)).2, hconn c hc]
      rfl
    change (W.card : ℤ) - (edgeSupport H W).card + edgeComponents H W =
      ((∑ c ∈ comps, beta H (U c) : ℕ) : ℤ)
    rw [hb, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have he' := congrArg (fun n : ℕ => (n : ℤ)) he
    have hs' := congrArg (fun n : ℕ => (n : ℤ)) hs
    simp only [Nat.cast_sum] at he' hs'
    rw [← he', ← hs']
    simp [edgeComponents, comps]
  · simp [beta, edgeSupport, edgeComponents]


end BuyAtBulk.EdgeOnlyGap
