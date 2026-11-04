import BuyAtBulk.UpperBound.AttachmentAuxTrace
import BuyAtBulk.UpperBound.FiniteGrid

/-! Original-request and finite-grid identities for every actual paid
auxiliary event, with above-cutoff scales and multiplicity retained. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

def RequestAuxMetadata (budget allowance : ℚ) (h ratio : ℕ) (events : List (AuxiliaryEvent G)) : Prop :=
  ∀ event ∈ events, event.allowance = allowance ∧ cutoff budget h ratio < event.edge.scale ∧
    ∃ depth ≤ gridDepth h ratio, event.edge.scale = gridScale budget ratio depth

namespace RequestAuxMetadata

theorem append {budget allowance : ℚ} {h ratio : ℕ} {first second : List (AuxiliaryEvent G)}
    (left : RequestAuxMetadata budget allowance h ratio first) (right : RequestAuxMetadata budget allowance h ratio second) :
    RequestAuxMetadata budget allowance h ratio (first ++ second) := by
  intro event member
  cases List.mem_append.mp member with
  | inl h => exact left event h
  | inr h => exact right event h

theorem of_attachment {budget allowance : ℚ} {h ratio d fuel : ℕ} {events : List (AuxiliaryEvent G)}
    (budget_nonneg : 0 ≤ budget) (h_pos : 0 < h) (ratio_ge : 2 ≤ ratio)
    (metadata : AttachmentAuxMetadata allowance (gridScale budget ratio d / (ratio : ℚ)) ratio
      (cutoff budget h ratio) fuel events) : RequestAuxMetadata budget allowance h ratio events := by
  intro event member
  obtain ⟨allowance_eq, above, depth, depth_le, scale_eq⟩ := metadata event member
  have grid_eq : event.edge.scale = gridScale budget ratio (d+1+depth) := by
    rw [scale_eq]
    simp only [gridScale, pow_add, pow_one, div_div, mul_assoc]
  have index_lt := active_scale_depth_lt budget h ratio (d+1+depth) budget_nonneg h_pos ratio_ge (by simpa only [← grid_eq] using above)
  exact ⟨allowance_eq, above, d+1+depth, index_lt.le, grid_eq⟩

end RequestAuxMetadata

theorem auxiliaryBounds_append (buying physical : V → ℚ) (ratio : ℚ) (first second : List (AuxiliaryEvent G))
    (left : ∀ event ∈ first, AuxiliaryBounds G buying physical ratio event)
    (right : ∀ event ∈ second, AuxiliaryBounds G buying physical ratio event) :
    ∀ event ∈ first ++ second, AuxiliaryBounds G buying physical ratio event := by
  intro event member
  cases List.mem_append.mp member with
  | inl h => exact left event h
  | inr h => exact right event h

theorem birthEdgesNonloop_append (first second : List (AuxiliaryEvent G))
    (left : BirthEdgesNonloop G first) (right : BirthEdgesNonloop G second) : BirthEdgesNonloop G (first ++ second) := by
  intro event member
  cases List.mem_append.mp member with
  | inl h => exact left event h
  | inr h => exact right event h

end BuyAtBulk.UpperBound
