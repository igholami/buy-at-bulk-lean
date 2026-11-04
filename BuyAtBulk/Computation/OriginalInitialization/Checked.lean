import BuyAtBulk.Computation.OriginalInitialization.Feasibility

/-! Explicit computed feasible input or computed disconnected-request index. -/
set_option maxHeartbeats 1800000
namespace BuyAtBulk.Computation.StoredOriginal
open OriginalPipeline
variable {n resources requests : ℕ} (tables : Tables n resources requests)

/-- Either a computed feasible unit-path initialization or an actual failing
request index. The latter is found by a finite scan, never existential choice. -/
def initializeChecked : Except (Fin requests) (Fractional tables) :=
  match initialized : initializeSeed tables with
  | some fractional => .ok fractional
  | none => .error ((failedRequest tables (List.finRange requests)).get (by
      apply (failedRequest_isSome tables _).mpr
      apply (seedEntries_none_iff tables _).mpr
      obtain ⟨i, disconnected⟩ := (initializeSeed_none_iff tables).mp initialized
      exact ⟨i, List.mem_finRange i, disconnected⟩))

def InitializationSpec : Except (Fin requests) (Fractional tables) → Prop
  | .error i =>
      ¬ Nonempty (tables.graphData.graph.Path (tables.graphData.source i) (tables.graphData.target i)) ∧
      ¬ Nonempty (OriginalFractional tables.graphData) ∧
      ¬ Nonempty (∀ i, tables.graphData.graph.Path (tables.graphData.source i) (tables.graphData.target i))
  | .ok fractional =>
      initializeSeed tables = some fractional ∧
      fractional.opening = Vector.replicate resources 1 ∧
      fractional.entries.map (fun entry => entry.1) = List.finRange requests ∧
      (∀ entry ∈ fractional.entries, entry.2.1 = 1) ∧
      ∀ entry ∈ fractional.entries, seedPath tables entry.1 = some entry.2.2


end BuyAtBulk.Computation.StoredOriginal
