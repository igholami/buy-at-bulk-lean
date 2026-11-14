import BuyAtBulk.EdgeOnlyGap.Items.CycleRank
import BuyAtBulk.EdgeOnlyGap.Items.GirthAtLeast
import BuyAtBulk.EdgeOnlyGap.Items.EvenSubgraphCycle
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofACycleNullity

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 2: connected m-edge witnesses; acyclic below girth. -/
theorem connectedRank (H : FiniteGraph) (g : ℕ) (W : Finset (Edges H))
    (connected : edgeComponents H W = 1) (nonempty : W.Nonempty)
    (girth : GirthAtLeast H g) :
  (beta H W : ℤ) = (W.card:ℤ) - (edgeSupport H W).card + 1 ∧
    (W.card < g → beta H W = 0) := by
  classical
  refine ⟨?_, ?_⟩
  · have h := (cycleRankFormula H W).2
    simpa only [connected, Nat.cast_one] using h
  · intro hshort
    have hzero : ∀ x : cycleSpace H W, x = 0 := by
      intro x
      apply Subtype.ext
      by_contra hxn
      let z : Edges H → ZMod 2 := fun e => if he : e ∈ W then x.val ⟨e, he⟩ else 0
      have hz : z ≠ 0 := by
        intro heq
        apply hxn
        funext e
        have h := congrFun heq e.val
        simpa [z, e.prop] using h
      have hboundary : ∀ v, baseBoundary H z v = 0 := by
        intro v
        have hx : (boundary H W) x.val v = 0 := congrFun x.prop v
        have hsum : (boundary H W) x.val v =
            ∑ e ∈ W, if v = e.val.1 ∨ v = e.val.2 then z e else 0 := by
          rw [← Finset.sum_coe_sort]
          change (∑ e : {e // e ∈ W}, if v = e.val.val.1 ∨ v = e.val.val.2 then x.val e else 0) = _
          apply Finset.sum_congr rfl
          intro e _
          simp only [z, dif_pos e.prop]
        rw [hsum] at hx
        calc
          baseBoundary H z v = ∑ e ∈ W, if v = e.val.1 ∨ v = e.val.2 then z e else 0 := by
            unfold baseBoundary
            symm
            apply Finset.sum_subset (Finset.subset_univ W)
            intro e _ he
            simp [z, he]
          _ = 0 := hx
      obtain ⟨v, w, hw, hlen, _⟩ := evenSubgraphCycle H z hz hboundary
      have hcard : (Finset.univ.filter fun e => z e ≠ 0).card ≤ W.card := by
        apply Finset.card_le_card
        intro e he
        by_contra hn
        have := (Finset.mem_filter.mp he).2
        exact this (by simp [z, hn])
      have hg : g ≤ w.length := by
        have h := (SimpleGraph.le_egirth.mp girth) v w hw
        exact_mod_cast h
      omega
    letI : Subsingleton (cycleSpace H W) := ⟨fun x y => (hzero x).trans (hzero y).symm⟩
    rw [← ProofA.cycleNullity H W]
    exact Module.finrank_zero_of_subsingleton


end BuyAtBulk.EdgeOnlyGap
