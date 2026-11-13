import BuyAtBulk.EdgeOnlyGap.Helpers.ProofAFiniteUnion
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofADFSCounts
import BuyAtBulk.EdgeOnlyGap.Items.ScriptProbability
import BuyAtBulk.EdgeOnlyGap.Items.ScriptCount
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

/-- Union over all variable-length scripts, retaining the exact query and surplus constraints. -/
 theorem witnessProbability (H : FiniteGraph) (q d T m : ℕ) (ports : PortTable H d)
    (root : Fin H.n × Fin q) (z : ℝ) (hd : 4 ≤ d) (hm : 1 ≤ m)
    (hT : 4 ≤ T) (hq : 8*T ≤ q) (hmT : m ≤ T) :
    liftProbability H q (fun π => ∃ script : List (DFSSymbol d),
      script.length ≤ 2*m ∧ (script.filter Option.isSome).length = m ∧
      z < ((script.filter surplusSymbol).length:ℝ) ∧
      ∃ st, dfsReplay H q d ports π root script = some st) ≤
      (liftA d:ℝ)^m * Real.rpow (4*T/(q:ℝ)) z := by
  classical
  let S := {s : List (DFSSymbol d) // s.length ≤ 2*m}
  letI : Finite S := boundedLists_finite (DFSSymbol d) (2*m)
  letI : Fintype S := Fintype.ofFinite S
  let E : S → Lift H q → Prop := fun s π =>
    (s.val.filter Option.isSome).length = m ∧ z < ((s.val.filter surplusSymbol).length:ℝ) ∧
      ∃ st, dfsReplay H q d ports π root s.val = some st
  let p : ℝ := 4*T/(q:ℝ)
  have hp : 0 < p := by
    have hqt : 0 < q := by omega
    dsimp [p]
    positivity
  have hp1 : p ≤ 1 := by
    apply (div_le_one (by exact_mod_cast (show 0 < q by omega))).mpr
    exact_mod_cast (show 4*T ≤ q by omega)
  have heach (s : S) : finiteProbability (E s) ≤ Real.rpow p z := by
    by_cases hc : (s.val.filter Option.isSome).length = m ∧
        z < ((s.val.filter surplusSymbol).length:ℝ)
    · have hmono : finiteProbability (E s) ≤ liftProbability H q
          (fun π => ∃ st, dfsReplay H q d ports π root s.val = some st) :=
        probability_mono (fun _ h => h.2.2)
      have hscript := scriptProbability H q d T ports root s.val hT hq (by rw [hc.1]; exact hmT)
      have hexp : p^((s.val.filter surplusSymbol).length) ≤ Real.rpow p z := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_ge hp hp1 (le_of_lt hc.2)
      exact hmono.trans (hscript.trans hexp)
    · have he : E s = (fun _ => False) := by
        funext π
        apply propext
        exact ⟨fun h => hc ⟨h.1,h.2.1⟩, False.elim⟩
      rw [he]
      simpa [finiteProbability, Fintype.card_subtype] using (Real.rpow_nonneg (le_of_lt hp) z)
  calc
    liftProbability H q (fun π => ∃ script : List (DFSSymbol d),
        script.length ≤ 2*m ∧ (script.filter Option.isSome).length = m ∧
        z < ((script.filter surplusSymbol).length:ℝ) ∧
        ∃ st, dfsReplay H q d ports π root script = some st) =
        finiteProbability (fun π => ∃ s : S, E s π) := by
      apply probability_congr
      intro π
      constructor
      · rintro ⟨s,hlen,hq,hz,hrun⟩
        exact ⟨⟨s,hlen⟩,hq,hz,hrun⟩
      · rintro ⟨s,hq,hz,hrun⟩
        exact ⟨s.val,s.prop,hq,hz,hrun⟩
    _ ≤ ∑ s : S, finiteProbability (E s) := probability_exists E
    _ ≤ ∑ _s : S, Real.rpow p z := Finset.sum_le_sum (fun s _ => heach s)
    _ = (Nat.card S:ℝ) * Real.rpow p z := by simp [Nat.card_eq_fintype_card]
    _ ≤ (liftA d:ℝ)^m * Real.rpow p z := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (le_of_lt hp) _)
      exact_mod_cast (le_trans (scriptCount d m hd hm).2.1 (scriptCount d m hd hm).2.2)

end BuyAtBulk.EdgeOnlyGap.ProofA
