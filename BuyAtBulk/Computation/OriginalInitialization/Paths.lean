import BuyAtBulk.Computation.StoredOriginal
import BuyAtBulk.Computation.ShortestPath

/-! Actual shortest paths and an actual failing request for original stored graphs. -/
set_option maxHeartbeats 1800000
namespace BuyAtBulk.Computation.StoredOriginal
open OriginalPipeline
variable {n resources requests : ℕ} (tables : Tables n resources requests)

def seedPath (i : Fin requests) :
    Option (tables.graphData.graph.Path (tables.graphData.source i) (tables.graphData.target i)) :=
  ShortestPath.shortestPath tables.graphData.graph (fun _ => 0)
    (tables.graphData.source i) (tables.graphData.target i)

theorem seedPath_none_iff (i : Fin requests) :
    seedPath tables i = none ↔
      ¬ Nonempty (tables.graphData.graph.Path (tables.graphData.source i) (tables.graphData.target i)) := by
  constructor
  · intro missing reachable
    obtain ⟨path, returned, _⟩ := ShortestPath.shortestPath_correct tables.graphData.graph (fun _ => 0)
      (fun _ => le_rfl) (tables.graphData.source i) (tables.graphData.target i) reachable
    rw [show ShortestPath.shortestPath tables.graphData.graph (fun _ => 0)
      (tables.graphData.source i) (tables.graphData.target i) = none from missing] at returned
    contradiction
  · intro disconnected
    cases result : seedPath tables i with
    | none => rfl
    | some path => exact False.elim (disconnected ⟨path⟩)

def seedEntries : List (Fin requests) →
    Option (List (Entry (G := tables.graphData.graph) tables.graphData.source tables.graphData.target))
  | [] => some []
  | i :: rest =>
    match seedPath tables i with
    | none => none
    | some path => (seedEntries rest).map fun entries => ⟨i, 1, path⟩ :: entries

theorem seedEntries_indices (order : List (Fin requests))
    (entries : List (Entry (G := tables.graphData.graph) tables.graphData.source tables.graphData.target))
    (returned : seedEntries tables order = some entries) :
    entries.map (fun entry => entry.1) = order ∧ ∀ entry ∈ entries, entry.2.1 = 1 := by
  induction order generalizing entries with
  | nil => simp only [seedEntries, Option.some.injEq] at returned; subst entries; simp
  | cons i rest ih =>
    simp only [seedEntries] at returned
    split at returned
    · contradiction
    · obtain ⟨tail, tail_returned, rfl⟩ := Option.map_eq_some_iff.mp returned
      obtain ⟨indices, weights⟩ := ih tail tail_returned
      constructor
      · simp [indices]
      · intro entry member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · rfl
        · exact weights entry member

theorem seedEntries_provenance (order : List (Fin requests))
    (entries : List (Entry (G := tables.graphData.graph) tables.graphData.source tables.graphData.target))
    (returned : seedEntries tables order = some entries) :
    ∀ entry ∈ entries, seedPath tables entry.1 = some entry.2.2 := by
  induction order generalizing entries with
  | nil => simp only [seedEntries, Option.some.injEq] at returned; subst entries; simp
  | cons i rest ih =>
    cases head : seedPath tables i with
    | none => simp only [seedEntries, head] at returned; contradiction
    | some path =>
      simp only [seedEntries, head] at returned
      obtain ⟨tail, tail_returned, rfl⟩ := Option.map_eq_some_iff.mp returned
      intro entry member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact head
      · exact ih tail tail_returned entry member

theorem seedEntries_none_iff (order : List (Fin requests)) :
    seedEntries tables order = none ↔ ∃ i ∈ order,
      ¬ Nonempty (tables.graphData.graph.Path (tables.graphData.source i) (tables.graphData.target i)) := by
  induction order with
  | nil => simp [seedEntries]
  | cons i rest ih =>
    cases head : seedPath tables i with
    | none =>
      have disconnected := (seedPath_none_iff tables i).mp head
      constructor
      · intro _; exact ⟨i, by simp, disconnected⟩
      · intro _; simp only [seedEntries, head]
    | some path =>
      constructor
      · intro missing
        have tail_none : seedEntries tables rest = none := by
          cases tail : seedEntries tables rest with
          | none => rfl
          | some entries => simp only [seedEntries, head, tail, Option.map_some] at missing; contradiction
        obtain ⟨j, member, disconnected⟩ := ih.mp tail_none
        exact ⟨j, by simp [member], disconnected⟩
      · rintro ⟨j, member, disconnected⟩
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact False.elim (disconnected ⟨path⟩)
        · have tail_none := ih.mpr ⟨j, member, disconnected⟩
          simp only [seedEntries, head, tail_none, Option.map_none]

/-- Actual first failed request, found by repeating the finite SP scan only
when an explicit negative certificate is needed. -/
def failedRequest : List (Fin requests) → Option (Fin requests)
  | [] => none
  | i :: rest => match seedPath tables i with
    | none => some i
    | some _ => failedRequest rest

theorem failedRequest_some (order : List (Fin requests)) (i : Fin requests)
    (returned : failedRequest tables order = some i) :
    ¬ Nonempty (tables.graphData.graph.Path (tables.graphData.source i) (tables.graphData.target i)) := by
  induction order with
  | nil => simp only [failedRequest] at returned; contradiction
  | cons j rest ih =>
    cases head : seedPath tables j with
    | none =>
      simp only [failedRequest, head, Option.some.injEq] at returned
      subst i
      exact (seedPath_none_iff tables j).mp head
    | some path =>
      exact ih (by simpa only [failedRequest, head] using returned)

theorem failedRequest_isSome (order : List (Fin requests)) :
    (failedRequest tables order).isSome ↔ seedEntries tables order = none := by
  induction order with
  | nil => simp [failedRequest, seedEntries]
  | cons i rest ih =>
    cases head : seedPath tables i with
    | none => simp [failedRequest, seedEntries, head]
    | some path => simpa only [failedRequest, seedEntries, head, Option.map_eq_none_iff] using ih


end BuyAtBulk.Computation.StoredOriginal
