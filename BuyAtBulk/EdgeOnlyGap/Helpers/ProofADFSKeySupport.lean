import BuyAtBulk.EdgeOnlyGap.Helpers.ProofADFSSelectedStep
import BuyAtBulk.EdgeOnlyGap.Items.EdgeSupport

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

 theorem keyIncident_iff (H : FiniteGraph) (q : ℕ) (π : Lift H q)
    (ej : Edges H × Fin q) (x : Fin H.n × Fin q) :
    keyIncident H q π ej x ↔
      liftCode H q π x = (liftKeyEdge H q π ej).val.1 ∨
      liftCode H q π x = (liftKeyEdge H q π ej).val.2 := by
  have he := liftKeyEdge_sym2 H q π ej
  have hm := congrArg (fun z : Sym2 (Fin (lifted H q π).n) => liftCode H q π x ∈ z) he
  simpa only [Sym2.mem_iff,Equiv.apply_eq_iff_eq,keyIncident,keyLeft,keyRight] using
    (Iff.of_eq hm).symm

 theorem keySupport_image (H : FiniteGraph) (q : ℕ) (π : Lift H q)
    (allowed : Finset (Edges H × Fin q)) :
    (keySupport H q π allowed).image (liftCode H q π) =
      edgeSupport (lifted H q π) (allowed.image (liftKeyEdge H q π)) := by
  ext v
  simp only [Finset.mem_image,edgeSupport,Finset.mem_biUnion,Finset.mem_insert,
    Finset.mem_singleton,keySupport]
  constructor
  · rintro ⟨x,⟨ej,he,hx⟩,rfl⟩
    exact ⟨liftKeyEdge H q π ej,⟨ej,he,rfl⟩,(keyIncident_iff H q π ej x).mp hx⟩
  · rintro ⟨e,⟨ej,he,rfl⟩,hv⟩
    refine ⟨(liftCode H q π).symm v,⟨ej,he,?_⟩,by simp⟩
    exact (keyIncident_iff H q π ej _).mpr (by simpa using hv)

end BuyAtBulk.EdgeOnlyGap.ProofA
