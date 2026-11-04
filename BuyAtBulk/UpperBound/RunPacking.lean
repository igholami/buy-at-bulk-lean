import BuyAtBulk.UpperBound.FixedRows
import BuyAtBulk.UpperBound.BirthPacking
import BuyAtBulk.UpperBound.RunBirthTrace

/-! Fixed original helper rows instantiated by every actual birth in a sorted
run, including promotions. This completes the source packing/run connection. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.UpperBound.NodeLP

variable {V : Type} [Fintype V] {G : SimpleGraph V} {h : ℕ}
local instance runPackingLocalInst1 : DecidableEq V := Classical.decEq V
local instance runPackingLocalInst2 : DecidableRel G.Adj := Classical.decRel _
variable (lp : NodeLP G h)

theorem fixedRow_for_birth (allowance : Fin h → ℚ) (ratio : ℕ) (event : BirthEvent G)
    (guard : BirthGuard G lp.buying lp.physical event)
    (metadata : ∃ i : Fin h, event.allowance = allowance i ∧
      EndpointPair (lp.source i) (lp.target i) event.endpoint event.mate ∧
      ∃ depth < gridDepth h ratio, event.scale = gridScale lp.buyingBudget ratio depth) :
    ∃ row : lp.FixedRow allowance ratio,
      gridScale lp.buyingBudget ratio row.val.2.2 = event.scale ∧
      allowance row.val.1 = event.allowance ∧ lp.rowSource row.val.2.1 row.val.1 = event.endpoint := by
  obtain ⟨i, allowance_eq, pair, depth, depth_le, scale_eq⟩ := metadata
  have reachable : Nonempty (G.Path event.endpoint event.mate) := by
    rcases pair with ⟨endpoint, mate⟩ | ⟨endpoint, mate⟩
    · simpa only [endpoint, mate] using lp.reachable i
    · rw [endpoint, mate]
      exact ⟨(lp.reachable i).some.reverse⟩
  have inclusion := Tolls.no_short_original_included G lp.buying lp.physical lp.buying_nonneg event.before
    event.allowance event.scale (event.scale / 16) event.endpoint event.mate reachable guard.2
  rcases pair with ⟨endpoint, mate⟩ | ⟨endpoint, mate⟩
  · let raw : RawRow h ratio := ⟨i, false, ⟨depth, by omega⟩⟩
    have included : lp.IncludedRow allowance ratio raw := by
      simpa only [IncludedRow, raw, rowSource, rowMate, Bool.false_eq_true, if_false,
        ← allowance_eq, ← scale_eq, ← endpoint, ← mate] using inclusion
    refine ⟨⟨raw, included⟩, ?_, allowance_eq.symm, endpoint.symm⟩
    exact scale_eq.symm
  · let raw : RawRow h ratio := ⟨i, true, ⟨depth, by omega⟩⟩
    have included : lp.IncludedRow allowance ratio raw := by
      simpa only [IncludedRow, raw, rowSource, rowMate, if_true,
        ← allowance_eq, ← scale_eq, ← endpoint, ← mate] using inclusion
    refine ⟨⟨raw, included⟩, ?_, allowance_eq.symm, endpoint.symm⟩
    exact scale_eq.symm

/-- The source τ_kN_k bound for a whole actual ordered run. The helper is
computed from fixed original rows; no eventwise packing/separation is assumed. -/
theorem run_birth_packing (allowance : Fin h → ℚ) (ratio : ℕ)
    (budget_pos : 0 < lp.buyingBudget) (hh : 0 < h) (ratio_ge : 2 ≤ ratio)
    (allowance_pos : ∀ i, 0 < allowance i)
    (length_bound : ∀ i, lp.fractionalLength i ≤ allowance i / 64)
    (selection : Helper.Selection (lp.fixedTollData allowance ratio budget_pos ratio_ge allowance_pos length_bound) h)
    (thresholdFactor : ℚ) {order : List (Fin h)} {before after : RoundingState G}
    (execution : RunExec G lp.buying lp.physical lp.buyingBudget ratio thresholdFactor
      lp.source lp.target allowance order before after)
    (sorted : order.Pairwise fun i j => allowance i ≤ allowance j)
    (helper_bought : selection.nodes ⊆ before.bought) :
    ∃ events, BirthTrace G lp.buying lp.physical before events after ∧
      RunBirthMetadata lp.buyingBudget ratio lp.source lp.target allowance order events ∧
      ∀ depth : Fin (gridDepth h ratio + 1),
        gridScale lp.buyingBudget ratio depth *
          Fintype.card (BirthsAtScale events (gridScale lp.buyingBudget ratio depth)) ≤
            (1664 / 3 : ℚ) * lp.buyingBudget := by
  obtain ⟨events, trace, metadata, chronological⟩ := RunExec.birth_trace budget_pos hh ratio_ge execution sorted
  let D := lp.fixedTollData allowance ratio budget_pos ratio_ge allowance_pos length_bound
  have lookup : ∀ event ∈ events, ∃ row : lp.FixedRow allowance ratio,
      gridScale lp.buyingBudget ratio row.val.2.2 = event.scale ∧
      allowance row.val.1 = event.allowance ∧ lp.rowSource row.val.2.1 row.val.1 = event.endpoint := by
    intro event member
    obtain ⟨i, _, hl, pair, grid⟩ := metadata event member
    exact lp.fixedRow_for_birth allowance ratio event (BirthTrace.guards G trace event member) ⟨i, hl, pair, grid⟩
  refine ⟨events, trace, metadata, ?_⟩
  intro depth
  let scale := gridScale lp.buyingBudget ratio depth
  let birthRow : BirthsAtScale events scale → lp.FixedRow allowance ratio :=
    fun i => Classical.choose (lookup (events.get i.val) (List.get_mem ..))
  have row_match : ∀ i : BirthsAtScale events scale,
      gridScale lp.buyingBudget ratio (birthRow i).val.2.2 = (events.get i.val).scale ∧
      allowance (birthRow i).val.1 = (events.get i.val).allowance ∧
      lp.rowSource (birthRow i).val.2.1 (birthRow i).val.1 = (events.get i.val).endpoint :=
    fun i => Classical.choose_spec (lookup (events.get i.val) (List.get_mem ..))
  have radius_row_match : ∀ i, D.radius (birthRow i) = scale / 16 := by
    intro i
    change gridScale lp.buyingBudget ratio (birthRow i).val.2.2 / 16 = scale / 16
    rw [(row_match i).1, i.property]
  have toll_row_match : ∀ i v, D.toll (birthRow i) v = Tolls.row G lp.buying lp.physical
      (scale / (events.get i.val).allowance) (scale / 16) (events.get i.val).endpoint v := by
    intro i v
    change Tolls.row G lp.buying lp.physical
      (gridScale lp.buyingBudget ratio (birthRow i).val.2.2 / allowance (birthRow i).val.1)
      (gridScale lp.buyingBudget ratio (birthRow i).val.2.2 / 16)
      (lp.rowSource (birthRow i).val.2.1 (birthRow i).val.1) v = _
    rw [(row_match i).1, (row_match i).2.1, (row_match i).2.2, i.property]
  have event_allowance_pos : ∀ event ∈ events, 0 < event.allowance := by
    intro event member
    obtain ⟨i, _, hi, _, _⟩ := metadata event member
    simpa only [hi] using allowance_pos i
  exact actual_birth_packing D lp.physical lp.physical_nonneg h hh budget_pos
    (lp.fixedRow_card_bound allowance ratio hh ratio_ge) selection trace event_allowance_pos chronological helper_bought
    scale (lp.gridScale_pos budget_pos ratio ratio_ge depth) birthRow radius_row_match toll_row_match

end BuyAtBulk.UpperBound.NodeLP
