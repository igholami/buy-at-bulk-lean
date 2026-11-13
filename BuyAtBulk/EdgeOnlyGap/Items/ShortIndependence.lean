import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import BuyAtBulk.EdgeOnlyGap.Items.ShortProjection
import Mathlib.LinearAlgebra.StdBasis

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 800000 in
/-- P. 4: independent standard basis projections and dimensions of the image of Z. -/
theorem shortIndependence (H : FiniteGraph) (q d g : ℕ) (π : Lift H q) (hd : 0 < d)
    (hg : 4 ≤ g) (girth : GirthAtLeast H g)
    (r : (supplyData H q d π hd).toInstance.IntegralRouting) :
  LinearIndependent (ZMod 2) (fun i : {i : Fin (requests H) //
      coreTraversals H q d π hd r i < g-1} =>
    chainProjection H q d π hd r (routeChain H q d π hd r i.val)) ∧
  shortCount H q d g π hd r ≤ Module.finrank (ZMod 2)
    ((portKernel H q d π hd r).map (chainProjection H q d π hd r)) ∧
  Module.finrank (ZMod 2) ((portKernel H q d π hd r).map (chainProjection H q d π hd r)) ≤
    Module.finrank (ZMod 2) (portKernel H q d π hd r)  := by
  classical
  let I := {i : Fin (requests H) // coreTraversals H q d π hd r i < g - 1}
  let P := (portKernel H q d π hd r).map (chainProjection H q d π hd r)
  have hli : LinearIndependent (ZMod 2) (fun i : I =>
      chainProjection H q d π hd r (routeChain H q d π hd r i.val)) := by
    have h := (Pi.linearIndependent_single_one (Edges H) (ZMod 2)).comp
      (fun i : I => (Fintype.equivFin (Edges H)).symm i.val)
      ((Fintype.equivFin (Edges H)).symm.injective.comp Subtype.val_injective)
    have heq : (fun i : I => chainProjection H q d π hd r
        (routeChain H q d π hd r i.val)) =
        (fun i : I => Pi.single ((Fintype.equivFin (Edges H)).symm i.val) (1 : ZMod 2)) := by
      funext i
      exact shortProjection H q d g π hd hg girth r i.val i.property
    rw [heq]
    exact h
  refine ⟨hli, ?_, Submodule.finrank_map_le _ _⟩
  let v : I → P := fun i => ⟨chainProjection H q d π hd r
      (routeChain H q d π hd r i.val),
    Submodule.mem_map.mpr ⟨routeChain H q d π hd r i.val,
      ((projectionBoundary H q d π hd r).2 i.val).1, rfl⟩⟩
  have hliP : LinearIndependent (ZMod 2) v :=
    LinearIndependent.of_comp P.subtype hli
  have hcard := hliP.fintype_card_le_finrank
  simpa only [I, P, Fintype.card_subtype, shortCount] using hcard

end BuyAtBulk.EdgeOnlyGap
