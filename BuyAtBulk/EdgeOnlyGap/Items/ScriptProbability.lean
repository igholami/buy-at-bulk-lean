import BuyAtBulk.EdgeOnlyGap.Items.DFSEdges
import BuyAtBulk.EdgeOnlyGap.Items.Parameters
import BuyAtBulk.EdgeOnlyGap.Items.AdaptiveSurplus
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofADFSReplayHit
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofADFSFalseTimes

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Successive-conditioning bound, p. 2: fixed replay script; encountered vertices depend on previous exposures. -/
theorem scriptProbability (H : FiniteGraph) (q d T : ℕ) (ports : PortTable H d)
    (root : Fin H.n × Fin q) (script : List (DFSSymbol d))
    (hT : 4 ≤ T) (hq : 8*T ≤ q) (queries : (script.filter Option.isSome).length ≤ T) :
  liftProbability H q (fun π => ∃ st, dfsReplay H q d ports π root script = some st) ≤
    (4*T/(q:ℝ))^((script.filter fun s => match s with | some (_,false) => true | _ => false).length) := by
  classical
  let indices := ProofA.falseTimes script
  have hbound : ∀ k ∈ indices, k < T := by
    intro k hk
    exact lt_of_lt_of_le (ProofA.falseTimes_spec script k hk).1 queries
  let embed : {k // k ∈ indices} → Fin T := fun k => ⟨k.val,hbound k.val k.property⟩
  let times : Finset (Fin T) := indices.attach.image embed
  have hinj : Function.Injective embed := by
    intro a b hab
    exact Subtype.ext (congrArg Fin.val hab)
  have hcard : times.card = (script.filter ProofA.surplusSymbol).length := by
    rw [Finset.card_image_of_injective _ hinj,Finset.card_attach]
    exact ProofA.falseTimes_card script
  have hsub : liftProbability H q
      (fun π => ∃ st, dfsReplay H q d ports π root script = some st) ≤
      liftProbability H q (fun π => ∀ t ∈ times,
        ProofA.adaptiveHit H q T (ProofA.historyPolicy H q d T ports root script)
          (ProofA.historyOld H q d T ports root script) t.val π) := by
    apply ProofA.probability_mono
    rintro π ⟨final,run⟩ t ht
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hk,p,ss,hs⟩ := ProofA.falseTimes_spec script k.val k.property
    exact ProofA.dfsReplay_false_hit H q d T ports π root script final run queries
      k.val hk p ss hs
  have hprob := adaptiveSurplus H q T (ProofA.historyPolicy H q d T ports root script)
    (ProofA.historyOld H q d T ports root script)
    (ProofA.historyOld_small H q d T ports root script) hT hq times
  rw [hcard] at hprob
  exact hsub.trans hprob

end BuyAtBulk.EdgeOnlyGap
