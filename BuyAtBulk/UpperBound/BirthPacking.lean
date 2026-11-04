import BuyAtBulk.UpperBound.BirthSeparation
import BuyAtBulk.UpperBound.Packing
import Mathlib.Data.List.Pairwise

/-! Lemma 4.6 instantiated on chronological actual births. Indices are retained
rather than deduplicating records, so promotions are charged individually. -/
noncomputable section
namespace BuyAtBulk.UpperBound

variable {V R : Type} [Fintype V] [Fintype R] [DecidableEq V] {G : SimpleGraph V}

abbrev BirthsAtScale (events : List (BirthEvent G)) (scale : ℚ) :=
  {i : Fin events.length // (events.get i).scale = scale}

/-- Every actual trace of births with nondecreasing allowances satisfies the
source constant, using its original rows and the explicitly constructed helper. -/
theorem actual_birth_packing (D : Helper.TollData V R) (physical : V → ℚ)
    (physical_nonneg : ∀ v, 0 ≤ physical v) (h : ℕ) (hh : 0 < h)
    (budget_pos : 0 < D.budget) (row_count : Fintype.card R ≤ (8 * h) ^ 2)
    (selection : Helper.Selection D h)
    {before after : RoundingState G} {events : List (BirthEvent G)}
    (trace : BirthTrace G D.buying physical before events after)
    (allowance_pos : ∀ event ∈ events, 0 < event.allowance)
    (sorted : events.Pairwise fun earlier later => earlier.allowance ≤ later.allowance)
    (helper_bought : selection.nodes ⊆ before.bought) (scale : ℚ) (scale_pos : 0 < scale)
    (birthRow : BirthsAtScale events scale → R)
    (radius_matches : ∀ i, D.radius (birthRow i) = scale / 16)
    (toll_matches : ∀ i v, D.toll (birthRow i) v = Tolls.row G D.buying physical
      (scale / (events.get i.val).allowance) (scale / 16) (events.get i.val).endpoint v) :
    scale * Fintype.card (BirthsAtScale events scale) ≤ (1664 / 3 : ℚ) * D.budget := by
  classical
  have pairs := trace.toll_rows_pairwise_separated D.buying_nonneg physical_nonneg allowance_pos
    sorted (selection.nodes) helper_bought scale scale_pos
  have separation : ∀ v ∈ selection.nodes, ∀ i j : BirthsAtScale events scale, i ≠ j →
      ¬ (0 < D.toll (birthRow i) v ∧ 0 < D.toll (birthRow j) v) := by
    intro v hv i j hij
    have indices_ne : i.val ≠ j.val := fun heq => hij (Subtype.ext heq)
    rw [toll_matches, toll_matches]
    by_cases earlier : i.val < j.val
    · exact List.pairwise_iff_get.mp pairs i.val j.val earlier i.property j.property v hv
    · have later : j.val < i.val := lt_of_le_of_ne (not_lt.mp earlier) (Ne.symm indices_ne)
      have rev := List.pairwise_iff_get.mp pairs j.val i.val later j.property i.property v hv
      exact fun hp => rev ⟨hp.2, hp.1⟩
  have packing := Packing.packing_from_separated_rows D h hh budget_pos row_count selection
    birthRow (scale / 16) radius_matches separation
  convert packing using 1 <;> ring

end BuyAtBulk.UpperBound
