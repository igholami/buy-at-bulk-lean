import BuyAtBulk.Computation.OriginalInitialization.Checked

/-! Verified graph-only feasible initialization and exact negative output. This is not an LP optimizer or an approximation guarantee relative to OPT. -/
set_option maxHeartbeats 1800000
namespace BuyAtBulk.Computation.StoredOriginal
open OriginalPipeline
variable {n resources requests : ℕ} (tables : Tables n resources requests)

theorem initializeChecked_correct : InitializationSpec tables (initializeChecked tables) := by
  unfold initializeChecked
  split
  · rename_i fractional returned
    obtain ⟨entries, computed, entries_eq, opening_eq⟩ := initializeSeed_spec tables fractional returned
    obtain ⟨indices, weights⟩ := seedEntries_indices tables _ entries computed
    refine ⟨returned, opening_eq, ?_, ?_, ?_⟩
    · simpa only [entries_eq] using indices
    · simpa only [entries_eq] using weights
    · simpa only [entries_eq] using seedEntries_provenance tables _ entries computed
  · rename_i missing
    have selected := Option.some_get (show (failedRequest tables (List.finRange requests)).isSome from by
      apply (failedRequest_isSome tables _).mpr
      apply (seedEntries_none_iff tables _).mpr
      obtain ⟨i, disconnected⟩ := (initializeSeed_none_iff tables).mp missing
      exact ⟨i, List.mem_finRange i, disconnected⟩)
    have disconnected := failedRequest_some tables _ _ selected.symm
    exact ⟨disconnected, disconnected_no_fractional tables ⟨_, disconnected⟩,
      disconnected_no_routing tables ⟨_, disconnected⟩⟩

end BuyAtBulk.Computation.StoredOriginal
