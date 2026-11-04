import BuyAtBulk.Computation.FlowDecomposition.Trace
import BuyAtBulk.Computation.FlowDecomposition.Schedule

/-! Verified executable decomposition of stored compact commodity flows.
The contract includes actual returned paths, unit mass, arc domination,
polynomial support/path size, fixed-denominator word bounds and an honest
candidate-search schedule. It does not implement an LP optimizer. -/
namespace BuyAtBulk.Computation.FlowDecomposition
open BuyAtBulk.CompactFlow
variable {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

theorem weighted_path_cells (numbering : V ≃ Fin n) (source target : V) (entries : WeightedPaths G source target) :
    (entries.map fun entry => entry.2.val.support.length).sum ≤ entries.length * n := by
  induction entries with
  | nil => simp
  | cons entry rest ih =>
    have first := entry.2.property.length_lt
    simp only [numbered_card numbering] at first
    simp only [SimpleGraph.Walk.length_support] at ih
    simp only [List.map_cons, List.sum_cons, List.length_cons, SimpleGraph.Walk.length_support]
    nlinarith

structure VerifiedDecomposition (matrix : FlowMatrix n) (source target : V)
    (entries : WeightedPaths G source target) : Prop where
  returned : decompose G numbering matrix source target = some entries
  weights_positive : ∀ entry ∈ entries, 0 < entry.1
  unit : (entries.map Prod.fst).sum = 1
  arc_dominated : ∀ u v,
    (entries.map fun entry => entry.1 * transportVisits entry.2.val u v).sum ≤ decodedFlow numbering matrix u v
  sparse : entries.length ≤ n * n + 1
  path_cells : (entries.map fun entry => entry.2.val.support.length).sum ≤ (n * n + 1) * n
  weight_words : ∀ entry ∈ entries,
    HasDenominator (commonDenominator matrix) entry.1 ∧
    scaledNumerator (commonDenominator matrix) entry.1 ≤ commonDenominator matrix ∧
    (Rational.Code.ofRat entry.1).bits ≤ 2 * denominatorInputBits matrix + 4
  traced_returned : (extractTraced G numbering source target (n * n + 1) matrix 1).1 = some entries
  state_words : ∀ state ∈ (extractTraced G numbering source target (n * n + 1) matrix 1).2,
    (Rational.Code.ofRat state.2).bits ≤ 2 * denominatorInputBits matrix + 4 ∧
    ∀ u v, (Rational.Code.ofRat (decodedFlow numbering state.1 u v)).bits ≤ 2 * denominatorInputBits matrix + 4
  scheduled_returned : (extractScheduled G numbering source target (n * n + 1) matrix 1).1 = some entries
  search_visits : (extractScheduled G numbering source target (n * n + 1) matrix 1).2 ≤
    (n * n + 1) * (2 * n ^ 3 + n)
  search_storage : ∀ state ∈ (extractTraced G numbering source target (n * n + 1) matrix 1).2,
    (iterate G numbering (decodedFlow numbering state.1) source n).length ≤ n ∧
    ((iterate G numbering (decodedFlow numbering state.1) source n).map fun entry => entry.2.length).sum ≤ n * n

/-- Every feasible stored unit transport flow has the actual computed sparse
path decomposition, with no classical selection of any output path or weight. -/
theorem decompose_verified (matrix : FlowMatrix n) (source target : V)
    (nonneg : ∀ u v, 0 ≤ decodedFlow numbering matrix u v) (le_one : ∀ u v, decodedFlow numbering matrix u v ≤ 1)
    (nonedge : ∀ u v, ¬G.Adj u v → decodedFlow numbering matrix u v = 0)
    (balance : ∀ v, (∑ u, decodedFlow numbering matrix v u) - (∑ u, decodedFlow numbering matrix u v) =
      (if source = v then 1 else 0) - (if target = v then 1 else 0)) :
    ∃ entries : WeightedPaths G source target, VerifiedDecomposition G numbering matrix source target entries := by
  obtain ⟨entries, returned, positive, mass, cap, length, encoding⟩ :=
    decompose_encoding G numbering matrix source target nonneg nonedge balance
  have cells := weighted_path_cells G numbering source target entries
  have schedule := decomposition_search_schedule G numbering matrix source target
  refine ⟨entries, returned, positive, mass, cap, length,
    cells.trans (Nat.mul_le_mul_right n length), encoding, ?_,
    decompose_trace_bits G numbering matrix source target nonneg le_one nonedge balance, ?_, schedule.2, ?_⟩
  · exact (extractTraced_value G numbering source target _ matrix _).trans returned
  · exact schedule.1.trans returned
  · intro state _
    exact search_storage G numbering (decodedFlow numbering state.1) source n

end BuyAtBulk.Computation.FlowDecomposition
