import BuyAtBulk.EdgeOnlyGap.Items.FractionalWitness
import BuyAtBulk.EdgeOnlyGap.Items.EdgeOnlyInstance

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 3: finite simple supply, full edge coverage, every request routable. -/
theorem supplyValidity (H : FiniteGraph) (q d : ℕ) (π : Lift H q) (hd : 0 < d)
    (hq : 0 < q) :
    EdgeOnlyInstance (supplyData H q d π hd) ∧
    Nonempty (supplyData H q d π hd).toInstance.IntegralRouting := by
  classical
  let D := supplyData H q d π hd
  let G := supplyGraph H q π
  let enum := (Fintype.equivFin G.edgeSet).symm
  let req := (Fintype.equivFin (Edges H)).symm
  refine ⟨⟨fun _ => rfl, fun a => ⟨(enum a).val, rfl⟩, fun e he => ?_⟩, ?_⟩
  · refine ⟨enum.symm ⟨e, he⟩, ?_⟩
    change Sum.inr (enum (enum.symm ⟨e, he⟩)).val = Sum.inr e
    simp <;> rfl
  · let j₀ : Fin q := ⟨0, hq⟩
    exact ⟨{
      path := fun i => D.encode i (witnessPath H q π (req i) j₀)
      allowed_path := fun i => D.allowed_encode i (witnessPath H q π (req i) j₀) }⟩

end BuyAtBulk.EdgeOnlyGap
