import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import BuyAtBulk.EdgeOnlyGap.Items.ComponentEdgeCounts
import BuyAtBulk.EdgeOnlyGap.Items.CycleRankDimension
import BuyAtBulk.EdgeOnlyGap.Items.CycleRank

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

private lemma walk_in_component_reachable (H : FiniteGraph) (W : Finset (Edges H))
    (c : (edgeSubgraph H W).ConnectedComponent) :
    ∀ {u v : Fin H.n} (w : (edgeSubgraph H W).Walk u v),
      (edgeSubgraph H W).connectedComponentMk u = c →
      (edgeSubgraph H (W.filter fun e => (edgeSubgraph H W).connectedComponentMk e.val.1 = c)).Reachable u v := by
  intro u v w
  induction w with
  | nil =>
    intro _
    exact SimpleGraph.Reachable.refl _
  | @cons u x v hadj rest ih =>
    intro hu
    have hx : (edgeSubgraph H W).connectedComponentMk x = c := by
      rw [← hu]
      exact (SimpleGraph.ConnectedComponent.eq.mpr hadj.reachable).symm
    have hadjU : (edgeSubgraph H (W.filter fun e => (edgeSubgraph H W).connectedComponentMk e.val.1 = c)).Adj u x := by
      unfold edgeSubgraph at hadj ⊢
      rw [SimpleGraph.fromRel_adj] at hadj ⊢
      rcases hadj with ⟨hne, ⟨e, heW, rfl, rfl⟩ | ⟨e, heW, rfl, rfl⟩⟩
      · refine ⟨hne, Or.inl ⟨e, ?_, rfl, rfl⟩⟩
        rw [Finset.mem_filter]
        exact ⟨heW, hu⟩
      · refine ⟨hne, Or.inr ⟨e, ?_, rfl, rfl⟩⟩
        rw [Finset.mem_filter]
        exact ⟨heW, hx⟩
    exact hadjU.reachable.trans (ih hx)

/-- P. 2: a disconnected violation has a connected violating component. -/
theorem connectedViolation (H : FiniteGraph) (g : ℕ) (W : Finset (Edges H))
    (bad : (2:ℚ)*W.card/g < beta H W) :
  ∃ U : Finset (Edges H), U ⊆ W ∧ edgeComponents H U = 1 ∧
    U.Nonempty ∧ (2:ℚ)*U.card/g < beta H U := by
  classical
  let comps := (edgeSupport H W).image (edgeSubgraph H W).connectedComponentMk
  let compEdges (c : (edgeSubgraph H W).ConnectedComponent) :=
    W.filter fun e => (edgeSubgraph H W).connectedComponentMk e.val.1 = c
  have hcard := componentEdgeCounts H W
  have hbeta := (cycleRankDimension H W).2.1
  have hsum_lt : ∑ c ∈ comps, (2 : ℚ) * (compEdges c).card / g <
      ∑ c ∈ comps, (beta H (compEdges c) : ℚ) := by
    have h1 : (2 : ℚ) * W.card / g = ∑ c ∈ comps, (2 : ℚ) * (compEdges c).card / g := by
      rw [hcard, Nat.cast_sum, Finset.mul_sum]
      simp only [div_eq_mul_inv, Finset.sum_mul]
      rfl
    have h2 : (beta H W : ℚ) = ∑ c ∈ comps, (beta H (compEdges c) : ℚ) := by
      rw [hbeta, Nat.cast_sum]
    rw [← h1, ← h2]
    exact bad
  obtain ⟨c, _, hc_lt⟩ := Finset.exists_lt_of_sum_lt hsum_lt
  let U := compEdges c
  have hU_sub : U ⊆ W := Finset.filter_subset _ _
  have hU_nonempty : U.Nonempty := by
    by_contra h_empty
    rw [Finset.not_nonempty_iff_eq_empty] at h_empty
    have h0 : beta H ∅ = 0 := (cycleRankDimension H W).2.2
    change (2 : ℚ) * U.card / g < beta H U at hc_lt
    rw [h_empty] at hc_lt
    simp [h0] at hc_lt
  refine ⟨U, hU_sub, ?_, hU_nonempty, hc_lt⟩
  unfold edgeComponents
  obtain ⟨e₀, he₀⟩ := hU_nonempty
  have he₀_supp : e₀.val.1 ∈ edgeSupport H U := by
    unfold edgeSupport
    rw [Finset.mem_biUnion]
    exact ⟨e₀, he₀, by simp⟩
  have h_all_eq : ∀ u ∈ edgeSupport H U,
      (edgeSubgraph H U).connectedComponentMk u = (edgeSubgraph H U).connectedComponentMk e₀.val.1 := by
    intro u hu
    have hu_c : (edgeSubgraph H W).connectedComponentMk u = c := by
      unfold edgeSupport at hu
      rw [Finset.mem_biUnion] at hu
      rcases hu with ⟨e, heU, hu_end⟩
      have he_c : (edgeSubgraph H W).connectedComponentMk e.val.1 = c :=
        (Finset.mem_filter.mp heU).2
      have heW : e ∈ W := (Finset.mem_filter.mp heU).1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu_end
      rcases hu_end with rfl | rfl
      · exact he_c
      · have hadj : (edgeSubgraph H W).Adj e.val.1 e.val.2 := by
          unfold edgeSubgraph
          rw [SimpleGraph.fromRel_adj]
          exact ⟨ne_of_lt e.prop.1, Or.inl ⟨e, heW, rfl, rfl⟩⟩
        rw [← he_c]
        exact (SimpleGraph.ConnectedComponent.eq.mpr hadj.reachable).symm
    have he₀_c : (edgeSubgraph H W).connectedComponentMk e₀.val.1 = c :=
      (Finset.mem_filter.mp he₀).2
    have hreachW : (edgeSubgraph H W).Reachable u e₀.val.1 :=
      SimpleGraph.ConnectedComponent.eq.mp (hu_c.trans he₀_c.symm)
    obtain ⟨w⟩ := hreachW
    exact SimpleGraph.ConnectedComponent.eq.mpr (walk_in_component_reachable H W c w hu_c)
  have himg : (edgeSupport H U).image (edgeSubgraph H U).connectedComponentMk =
      {(edgeSubgraph H U).connectedComponentMk e₀.val.1} := by
    ext x
    simp only [Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact h_all_eq u hu
    · rintro rfl
      exact ⟨e₀.val.1, he₀_supp, rfl⟩
  rw [himg, Finset.card_singleton]

end BuyAtBulk.EdgeOnlyGap
