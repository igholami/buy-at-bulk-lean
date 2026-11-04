import BuyAtBulk.Computation.OriginalInitialization.Paths

/-! Feasible stored unit-path initialization, or exact disconnection and impossibility. -/
set_option maxHeartbeats 1800000
namespace BuyAtBulk.Computation.StoredOriginal
open OriginalPipeline
variable {n resources requests : ℕ} (tables : Tables n resources requests)

section Mass
variable {V : Type} {G : SimpleGraph V} {h : ℕ} (source target : Fin h → V)

theorem selected_mass (entries : List (Entry (G := G) source target)) (i : Fin h) :
    ((selectPaths source target entries i).map Prod.fst).sum =
      (entries.map fun entry => if entry.1 = i then entry.2.1 else 0).sum := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨j, weight, path⟩
    by_cases same : j = i
    · subst j
      simp [selectPaths, List.filterMap_cons]
      simpa only [selectPaths] using ih
    · simp [selectPaths, List.filterMap_cons, same]
      simpa only [selectPaths] using ih

theorem selected_unit (entries : List (Entry (G := G) source target))
    (indices : entries.map (fun entry => entry.1) = List.finRange h)
    (weights : ∀ entry ∈ entries, entry.2.1 = 1) (i : Fin h) :
    ((selectPaths source target entries i).map Prod.fst).sum = 1 := by
  rw [selected_mass]
  calc
    (entries.map fun entry => if entry.1 = i then entry.2.1 else 0).sum =
        (entries.map fun entry => if entry.1 = i then (1 : ℚ) else 0).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro entry member
      rw [weights entry member]
    _ = ((List.finRange h).map fun j => if j = i then (1 : ℚ) else 0).sum := by
      rw [← indices, List.map_map]
      rfl
    _ = 1 := by rw [← Fin.sum_univ_def]; simp

end Mass

theorem seedEntries_unit
    (entries : List (Entry (G := tables.graphData.graph) tables.graphData.source tables.graphData.target))
    (returned : seedEntries tables (List.finRange requests) = some entries) (i : Fin requests) :
    ((selectPaths tables.graphData.source tables.graphData.target entries i).map Prod.fst).sum = 1 := by
  obtain ⟨indices, weights⟩ := seedEntries_indices tables _ entries returned
  exact selected_unit _ _ entries indices weights i

private theorem filtered_mass_le {P : Type} (entries : List (ℚ × P)) (used : P → Bool)
    (nonneg : ∀ entry ∈ entries, 0 ≤ entry.1) :
    (entries.map fun entry => if used entry.2 then entry.1 else 0).sum ≤ (entries.map Prod.fst).sum := by
  induction entries with
  | nil => simp
  | cons entry rest ih =>
    have head := nonneg entry (by simp)
    have tail := ih (fun e member => nonneg e (by simp [member]))
    simp only [List.map_cons, List.sum_cons]
    split_ifs <;> linarith

def initializeSeed : Option (Fractional tables) :=
  match returned : seedEntries tables (List.finRange requests) with
  | none => none
  | some entries => some {
      opening := Vector.replicate resources 1
      entries := entries
      opening_bounds := by intro a; simp
      nonneg := by
        intro entry member
        rw [(seedEntries_indices tables _ entries returned).2 entry member]
        norm_num
      unit := seedEntries_unit tables entries returned
      capacity := by
        intro i a
        have nonneg : ∀ entry ∈ entries, 0 ≤ entry.2.1 := by
          intro entry member
          rw [(seedEntries_indices tables _ entries returned).2 entry member]
          norm_num
        have selected_nonneg := selectPaths_nonneg _ _ entries nonneg i
        have bound := filtered_mass_le (selectPaths _ _ entries i) (fun path => usesResource tables.graphData i path a) selected_nonneg
        rw [seedEntries_unit tables entries returned i] at bound
        simpa using bound }

theorem initializeSeed_spec (fractional : Fractional tables)
    (returned : initializeSeed tables = some fractional) :
    ∃ entries,
      seedEntries tables (List.finRange requests) = some entries ∧
      fractional.entries = entries ∧ fractional.opening = Vector.replicate resources 1 := by
  unfold initializeSeed at returned
  split at returned
  · contradiction
  · rename_i entries computed
    simp only [Option.some.injEq] at returned
    subst fractional
    exact ⟨entries, computed, rfl, rfl⟩

theorem initializeSeed_none_iff : initializeSeed tables = none ↔
    ∃ i : Fin requests,
      ¬ Nonempty (tables.graphData.graph.Path (tables.graphData.source i) (tables.graphData.target i)) := by
  have missing := seedEntries_none_iff tables (List.finRange requests)
  simp only [List.mem_finRange, true_and] at missing
  unfold initializeSeed
  split
  · rename_i result
    exact ⟨fun _ => missing.mp result, fun _ => rfl⟩
  · rename_i entries result
    constructor
    · intro impossible; contradiction
    · intro disconnected
      have impossible := missing.mpr disconnected
      rw [result] at impossible
      contradiction

theorem disconnected_no_fractional
    (disconnected : ∃ i : Fin requests,
      ¬ Nonempty (tables.graphData.graph.Path (tables.graphData.source i) (tables.graphData.target i))) :
    ¬ Nonempty (OriginalFractional tables.graphData) := by
  rintro ⟨input⟩
  obtain ⟨i, disconnected⟩ := disconnected
  have unit := input.unit i
  cases paths : input.paths i with
  | nil => simp [paths] at unit
  | cons entry rest => exact disconnected ⟨entry.2⟩

theorem disconnected_no_routing
    (disconnected : ∃ i : Fin requests,
      ¬ Nonempty (tables.graphData.graph.Path (tables.graphData.source i) (tables.graphData.target i))) :
    ¬ Nonempty (∀ i, tables.graphData.graph.Path (tables.graphData.source i) (tables.graphData.target i)) := by
  rintro ⟨routing⟩
  obtain ⟨i, disconnected⟩ := disconnected
  exact disconnected ⟨routing i⟩

theorem initializeSeed_none_impossible (missing : initializeSeed tables = none) :
    ¬ Nonempty (Fractional tables) ∧
    ¬ Nonempty (∀ i, tables.graphData.graph.Path (tables.graphData.source i) (tables.graphData.target i)) := by
  have disconnected := (initializeSeed_none_iff tables).mp missing
  refine ⟨?_, disconnected_no_routing tables disconnected⟩
  rintro ⟨fractional⟩
  exact disconnected_no_fractional tables disconnected ⟨fractional.decode tables⟩


end BuyAtBulk.Computation.StoredOriginal
