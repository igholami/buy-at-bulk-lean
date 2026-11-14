import BuyAtBulk.EdgeOnlyGap.Items.ConnectedViolation
import BuyAtBulk.EdgeOnlyGap.Items.ConnectedRank
import BuyAtBulk.EdgeOnlyGap.Items.LiftGirth
import BuyAtBulk.EdgeOnlyGap.Items.DFSCompleteness
import BuyAtBulk.EdgeOnlyGap.Items.LocallySparse
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofADFSCounts
import Mathlib.Tactic

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

/-- The original bad event has a connected, rooted, bounded-length replay witness. -/
 theorem witnessEncoding (H : FiniteGraph) (q d g T : ℕ) (ports : PortTable H d)
    (girth : GirthAtLeast H g) (π : Lift H q) (bad : ¬LocallySparse H q g T π) :
    ∃ m ∈ Finset.Icc g T, ∃ root : Fin H.n × Fin q,
      ∃ script : List (DFSSymbol d), script.length ≤ 2*m ∧
        (script.filter Option.isSome).length = m ∧
        2*(m:ℝ)/g < ((script.filter surplusSymbol).length:ℝ) ∧
        ∃ st, dfsReplay H q d ports π root script = some st := by
  classical
  unfold LocallySparse at bad
  push_neg at bad
  obtain ⟨W,hW,bad⟩ := bad
  obtain ⟨U,hUW,hconn,hne,hbad⟩ := connectedViolation (lifted H q π) g W bad
  have hUT : U.card ≤ T := (Finset.card_le_card hUW).trans hW
  have hgm : g ≤ U.card := by
    by_contra hn
    have hz := (connectedRank (lifted H q π) g U hconn hne (liftGirth H q g π girth)).2 (by omega)
    rw [hz] at hbad
    have : (0:ℚ) ≤ 2*U.card/g := by positivity
    linarith
  obtain ⟨e,he⟩ := hne
  have hsupp : e.val.1 ∈ edgeSupport (lifted H q π) U := by
    unfold edgeSupport
    exact Finset.mem_biUnion.mpr ⟨e,he,by simp⟩
  let code : (Fin H.n × Fin q) ≃ Fin (lifted H q π).n :=
    (Fintype.equivFin (Fin H.n × Fin q)).trans (finCongr (by simp [lifted]))
  let root := code.symm e.val.1
  have hr : finCongr (by simp [lifted]) (Fintype.equivFin (Fin H.n × Fin q) root) ∈
      edgeSupport (lifted H q π) U := by
    change code (code.symm e.val.1) ∈ _
    simpa using hsupp
  obtain ⟨script,st,hrun,_,_,hqueries,_,hlen,hsurplus⟩ :=
    dfsCompleteness H q d ports π U hconn root hr
  refine ⟨U.card, Finset.mem_Icc.mpr ⟨hgm,hUT⟩,root,script,hlen,hqueries,?_,st,hrun⟩
  have heq := dfsReplay_surplus H q d ports π root script st hrun
  rw [← heq, hsurplus]
  have hh := (Rat.cast_lt (K := ℝ)).mpr hbad
  simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using hh

end BuyAtBulk.EdgeOnlyGap.ProofA
