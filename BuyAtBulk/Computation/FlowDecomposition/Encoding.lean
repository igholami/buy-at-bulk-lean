import BuyAtBulk.Computation.FlowDecomposition.Denominators
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! The actual returned sparse list has polynomial encoding length. Its
weights have one fixed common denominator with bit size bounded by the sum of
input denominator sizes; this does not depend on the numerical denominator. -/
namespace BuyAtBulk.Computation.FlowDecomposition
open BuyAtBulk.CompactFlow
variable {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

theorem decompose_encoding (matrix : FlowMatrix n) (source target : V)
    (nonneg : ∀ u v, 0 ≤ decodedFlow numbering matrix u v)
    (nonedge : ∀ u v, ¬G.Adj u v → decodedFlow numbering matrix u v = 0)
    (balance : ∀ v, (∑ u, decodedFlow numbering matrix v u) - (∑ u, decodedFlow numbering matrix u v) =
      (if source = v then 1 else 0) - (if target = v then 1 else 0)) :
    ∃ entries : WeightedPaths G source target,
      decompose G numbering matrix source target = some entries ∧
      (∀ entry ∈ entries, 0 < entry.1) ∧ (entries.map Prod.fst).sum = 1 ∧
      (∀ u v, (entries.map fun entry => entry.1 * transportVisits entry.2.val u v).sum ≤ decodedFlow numbering matrix u v) ∧
      entries.length ≤ n * n + 1 ∧
      ∀ entry ∈ entries,
        HasDenominator (commonDenominator matrix) entry.1 ∧
        scaledNumerator (commonDenominator matrix) entry.1 ≤ commonDenominator matrix ∧
        (Rational.Code.ofRat entry.1).bits ≤ 2 * denominatorInputBits matrix + 4 := by
  obtain ⟨entries, returned, positive, mass, capacity, length⟩ :=
    decompose_correct G numbering matrix source target nonneg nonedge balance
  have denominators := extract_denominator G numbering source target (n * n + 1) matrix 1
    (commonDenominator matrix) entries (by change (1 : ℕ) ∣ commonDenominator matrix; exact one_dvd _) (decoded_coordinate_denominator numbering matrix) returned
  refine ⟨entries, returned, positive, mass, capacity, length, ?_⟩
  intro entry member
  have denominator := denominators entry member
  have all_nonneg : ∀ q ∈ entries.map Prod.fst, (0 : ℚ) ≤ q := by
    intro q member
    obtain ⟨other, present, rfl⟩ := List.mem_map.mp member
    exact (positive other present).le
  have upper : entry.1 ≤ 1 := by
    have bound := List.single_le_sum all_nonneg entry.1 (List.mem_map.mpr ⟨entry, member, rfl⟩)
    simpa only [mass] using bound
  have lower := (positive entry member).le
  have bit_bound := unit_bits_bound entry.1 (commonDenominator matrix)
    (commonDenominator_pos matrix) denominator lower upper
  have input_bound := commonDenominator_bits matrix
  refine ⟨denominator, scaledNumerator_le entry.1 _ (commonDenominator_pos matrix) denominator lower upper, ?_⟩
  omega

end BuyAtBulk.Computation.FlowDecomposition
