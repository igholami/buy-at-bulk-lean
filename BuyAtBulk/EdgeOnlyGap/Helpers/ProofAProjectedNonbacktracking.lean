import BuyAtBulk.EdgeOnlyGap.Helpers.ProofALiftNeighborInjective
import Mathlib.Combinatorics.SimpleGraph.Paths

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA

/-- A simple lifted cycle projects without an immediate reversal. -/
theorem projectedNonbacktracking (H : FiniteGraph) (q : ℕ) (π : Lift H q)
    (v : Fin H.n × Fin q) (w : (liftGraph H q π).Walk v v) (hc : w.IsCycle) :
    ∀ i : ℕ, i + 2 ≤ w.length → (w.getVert i).1 ≠ (w.getVert (i + 2)).1 := by
  intro i hi he
  have hxy := liftNeighborInjective H q π (w.getVert (i + 1))
    (w.getVert i) (w.getVert (i + 2))
    (w.adj_getVert_succ (by omega)).symm
    (w.adj_getVert_succ (by omega)) he
  have hn := hc.getVert_sub_one_ne_getVert_add_one (i := i + 1) (by omega)
  apply hn
  simpa only [Nat.add_sub_cancel, Nat.add_assoc] using hxy

end BuyAtBulk.EdgeOnlyGap.ProofA
