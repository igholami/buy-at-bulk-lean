import Mathlib.Analysis.SpecialFunctions.Pow.Real
import BuyAtBulk.EdgeOnlyGap.Items.LocallySparse
import BuyAtBulk.EdgeOnlyGap.Items.GirthAtLeast
import BuyAtBulk.EdgeOnlyGap.Items.PortsExist
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofAWitnessEncoding
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofAWitnessProbability

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 2: union over roots, script lengths and surplus counts; fractional exponent via real power. -/
theorem witnessUnionBound (H : FiniteGraph) (q d g T : ℕ) (hd : 4 ≤ d) (hg : 4 ≤ g)
    (hq : 8*T ≤ q) (hT : g ≤ T) (degree : ∀ v, H.graph.degree v ≤ d)
    (girth : GirthAtLeast H g) :
  liftProbability H q (fun π => ¬ LocallySparse H q g T π) ≤
    (H.n:ℝ)*q * ∑ m ∈ Finset.Icc g T,
      (liftA d:ℝ)^m * Real.rpow (4*T/(q:ℝ)) (2*(m:ℝ)/g) := by
  classical
  obtain ⟨ports⟩ := portsExist H d degree
  let E := fun (m : ℕ) (root : Fin H.n × Fin q) (π : Lift H q) =>
    ∃ script : List (DFSSymbol d), script.length ≤ 2*m ∧
      (script.filter Option.isSome).length = m ∧
      2*(m:ℝ)/g < ((script.filter ProofA.surplusSymbol).length:ℝ) ∧
      ∃ st, dfsReplay H q d ports π root script = some st
  have hmBound (m : ℕ) (hm : m ∈ Finset.Icc g T) :
      finiteProbability (fun π => ∃ root, E m root π) ≤
        (H.n:ℝ)*q * ((liftA d:ℝ)^m * Real.rpow (4*T/(q:ℝ)) (2*(m:ℝ)/g)) := by
    have hmem := Finset.mem_Icc.mp hm
    calc
      finiteProbability (fun π => ∃ root, E m root π) ≤
          ∑ root : Fin H.n × Fin q, finiteProbability (E m root) :=
        ProofA.probability_exists (E m)
      _ ≤ ∑ _root : Fin H.n × Fin q,
          ((liftA d:ℝ)^m * Real.rpow (4*T/(q:ℝ)) (2*(m:ℝ)/g)) := by
        apply Finset.sum_le_sum
        intro root _
        exact ProofA.witnessProbability H q d T m ports root (2*(m:ℝ)/g)
          hd (by omega) (by omega) hq hmem.2
      _ = _ := by simp [Fintype.card_prod, Nat.cast_mul, mul_assoc]
  calc
    liftProbability H q (fun π => ¬LocallySparse H q g T π) ≤
        finiteProbability (fun π => ∃ m ∈ Finset.Icc g T, ∃ root, E m root π) := by
      apply ProofA.probability_mono
      intro π hbad
      exact ProofA.witnessEncoding H q d g T ports girth π hbad
    _ ≤ ∑ m ∈ Finset.Icc g T, finiteProbability (fun π => ∃ root, E m root π) :=
      ProofA.probability_union (Finset.Icc g T) (fun m π => ∃ root, E m root π)
    _ ≤ ∑ m ∈ Finset.Icc g T,
        (H.n:ℝ)*q * ((liftA d:ℝ)^m * Real.rpow (4*T/(q:ℝ)) (2*(m:ℝ)/g)) :=
      Finset.sum_le_sum hmBound
    _ = _ := by rw [Finset.mul_sum]

end BuyAtBulk.EdgeOnlyGap
