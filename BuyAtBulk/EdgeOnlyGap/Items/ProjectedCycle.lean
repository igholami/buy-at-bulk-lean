import Mathlib.Combinatorics.SimpleGraph.Paths
import BuyAtBulk.EdgeOnlyGap.Items.Lift
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofAProjectedNonbacktracking
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofANonbacktrackingCycle

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit cycle-projection and extraction claim, p. 2, used to prove lift girth. -/
theorem projectedCycle (H : FiniteGraph) (q : ℕ) (π : Lift H q)
    (v : Fin H.n × Fin q) (w : (liftGraph H q π).Walk v v) (cycle : w.IsCycle) :
  (∀ i : ℕ, ∀ h₁ : i < w.support.length, ∀ h₂ : i+2 < w.support.length,
    (w.support[i]'h₁).1 ≠ (w.support[i+2]'h₂).1) ∧
  ∃ (u : Fin H.n) (c : H.graph.Walk u u), c.IsCycle ∧ c.length ≤ w.length  := by
  have hnb := ProofA.projectedNonbacktracking H q π v w cycle
  constructor
  · intro i h₁ h₂ he
    have hi : i + 2 ≤ w.length := by
      rw [SimpleGraph.Walk.length_support] at h₂
      omega
    apply hnb i hi
    rw [w.getVert_eq_support_getElem (by omega), w.getVert_eq_support_getElem (by omega)]
    exact he
  · let hom : liftGraph H q π →g H.graph :=
      { toFun := Prod.fst
        map_rel' := by
          intro x y hxy
          unfold liftGraph at hxy
          rw [SimpleGraph.fromRel_adj] at hxy
          rcases hxy with ⟨_, ⟨e, hx, hy, _⟩ | ⟨e, hx, hy, _⟩⟩
          · rw [hx, hy]; exact e.prop.2
          · rw [hx, hy]; exact e.prop.2.symm }
    have hnb' : ∀ i : ℕ, i + 2 ≤ (w.map hom).length →
        (w.map hom).getVert i ≠ (w.map hom).getVert (i + 2) := by
      intro i hi
      rw [SimpleGraph.Walk.getVert_map, SimpleGraph.Walk.getVert_map]
      change (w.getVert i).1 ≠ (w.getVert (i + 2)).1
      exact hnb i (by simpa using hi)
    rcases ProofA.pathOrCycle (w.map hom) hnb' with hp | ⟨u, c, hc, hlen⟩
    · have hnil := SimpleGraph.Walk.isPath_iff_nil.mp hp
      have hlen : (w.map hom).length = 0 := by
        simpa only [SimpleGraph.Walk.length_eq_zero_iff] using hnil
      have hthree := cycle.three_le_length
      rw [SimpleGraph.Walk.length_map] at hlen
      omega
    · exact ⟨u, c, hc, by simpa only [SimpleGraph.Walk.length_map] using hlen⟩

end BuyAtBulk.EdgeOnlyGap
