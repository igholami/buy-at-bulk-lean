import BuyAtBulk.UpperBound.AttachmentBirthTrace
import BuyAtBulk.UpperBound.MainChoice

/-! Original request and common-grid identities carried by each concrete
birth log, including a proof that recursive above-cutoff births have depth
strictly less than `K`. The bottom grid position is excluded from the birth
accounting because it is at or below the cutoff. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

def RequestBirthMetadata (budget allowance : ℚ) (h ratio : ℕ) (s t : V)
    (events : List (BirthEvent G)) : Prop :=
  ∀ event ∈ events, event.allowance = allowance ∧ EndpointPair s t event.endpoint event.mate ∧
    ∃ depth < gridDepth h ratio, event.scale = gridScale budget ratio depth

namespace RequestBirthMetadata

theorem append {budget allowance : ℚ} {h ratio : ℕ} {s t : V} {first second : List (BirthEvent G)}
    (left : RequestBirthMetadata budget allowance h ratio s t first)
    (right : RequestBirthMetadata budget allowance h ratio s t second) :
    RequestBirthMetadata budget allowance h ratio s t (first ++ second) := by
  intro event member
  cases List.mem_append.mp member with
  | inl h => exact left event h
  | inr h => exact right event h

theorem of_assignment {budget allowance : ℚ} {h ratio d : ℕ} {s t endpoint mate : V}
    {events : List (BirthEvent G)} (index_lt : d < gridDepth h ratio)
    (pair : EndpointPair s t endpoint mate)
    (metadata : ∀ event ∈ events, event.endpoint = endpoint ∧ event.mate = mate ∧
      event.allowance = allowance ∧ event.scale = gridScale budget ratio d) :
    RequestBirthMetadata budget allowance h ratio s t events := by
  intro event member
  obtain ⟨endpoint_eq, mate_eq, allowance_eq, scale_eq⟩ := metadata event member
  exact ⟨allowance_eq, by simpa only [endpoint_eq, mate_eq] using pair, d, index_lt, scale_eq⟩

theorem of_attachment {budget allowance : ℚ} {h ratio d fuel : ℕ} {s t endpoint mate : V}
    {events : List (BirthEvent G)} (budget_nonneg : 0 ≤ budget) (h_pos : 0 < h) (ratio_ge : 2 ≤ ratio)
    (pair : EndpointPair s t endpoint mate)
    (metadata : AttachmentBirthMetadata allowance (gridScale budget ratio d / (ratio : ℚ)) ratio
      (cutoff budget h ratio) fuel endpoint mate events) :
    RequestBirthMetadata budget allowance h ratio s t events := by
  intro event member
  obtain ⟨endpoint_eq, mate_eq, allowance_eq, above, depth, depth_le, scale_eq⟩ := metadata event member
  have grid_eq : event.scale = gridScale budget ratio (d+1+depth) := by
    rw [scale_eq]
    simp only [gridScale, pow_add, pow_one, div_div, mul_assoc]
  have index_lt := active_scale_depth_lt budget h ratio (d+1+depth) budget_nonneg h_pos ratio_ge (by simpa only [← grid_eq] using above)
  exact ⟨allowance_eq, by simpa only [endpoint_eq, mate_eq] using pair, d+1+depth, index_lt, grid_eq⟩

end RequestBirthMetadata
end BuyAtBulk.UpperBound
