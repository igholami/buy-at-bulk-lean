import BuyAtBulk.EdgeOnlyGap.Items.ShortCycleSupport
import BuyAtBulk.EdgeOnlyGap.Items.GirthAtLeast
import BuyAtBulk.EdgeOnlyGap.Items.EvenSubgraphCycle

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Conclusion, p. 4: girth forces the projection to be exactly the demand basis vector. -/
theorem shortProjection (H : FiniteGraph) (q d g : ℕ) (π : Lift H q) (hd : 0 < d)
    (hg : 4 ≤ g) (girth : GirthAtLeast H g)
    (r : (supplyData H q d π hd).toInstance.IntegralRouting)
    (i : Fin (requests H)) (short : coreTraversals H q d π hd r i < g-1) :
  chainProjection H q d π hd r (routeChain H q d π hd r i) =
    Pi.single ((Fintype.equivFin (Edges H)).symm i) 1  := by
  classical
  let e := (Fintype.equivFin (Edges H)).symm i
  let y := chainProjection H q d π hd r (routeChain H q d π hd r i)
  have hs := shortCycleSupport H q d g π hd hg r i short
  have hz : y + Pi.single e (1 : ZMod 2) = 0 := by
    by_contra hne
    obtain ⟨v, w, hw, hlen, _⟩ := evenSubgraphCycle H _ hne hs.1
    have hge : g ≤ w.length := ENat.coe_le_coe.mp
      ((show (g : ℕ∞) ≤ H.graph.egirth from girth).trans hw.egirth_le_length)
    have hsmall : g ≤ g - 1 := hge.trans (hlen.trans hs.2)
    exact Nat.not_lt_of_ge hsmall (Nat.sub_lt (lt_of_lt_of_le (by decide : 0 < 4) hg) (by decide))
  let b : Edges H → ZMod 2 := Pi.single e 1
  funext a
  have ha : y a + b a = 0 := congrFun hz a
  have hb : b a + b a = 0 := by
    by_cases h : a = e <;> simp [b, Pi.single_apply, h] <;> decide
  change y a = b a
  calc
    y a = y a + (b a + b a) := by rw [hb, add_zero]
    _ = (y a + b a) + b a := (add_assoc _ _ _).symm
    _ = b a := by rw [ha, zero_add]

end BuyAtBulk.EdgeOnlyGap
