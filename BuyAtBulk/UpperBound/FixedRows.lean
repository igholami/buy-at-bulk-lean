import BuyAtBulk.UpperBound.NodeLPReverse
import BuyAtBulk.UpperBound.HelperResult

/-! The actual finite original endpoint/scale toll database, constructed from
the node LP before any purchases. No birth-dependent rows are introduced. -/
noncomputable section
namespace BuyAtBulk.UpperBound.NodeLP

variable {V : Type} [Fintype V] {G : SimpleGraph V} {h : ℕ}
local instance fixedRowsLocalInst1 : DecidableEq V := Classical.decEq V
local instance fixedRowsLocalInst2 : DecidableRel G.Adj := Classical.decRel _
variable (lp : NodeLP G h)

abbrev RawRow (h ratio : ℕ) := Fin h × Bool × Fin (gridDepth h ratio + 1)

def rowSource (side : Bool) (i : Fin h) : V := if side then lp.target i else lp.source i
def rowMate (side : Bool) (i : Fin h) : V := if side then lp.source i else lp.target i

def IncludedRow (allowance : Fin h → ℚ) (ratio : ℕ) (raw : RawRow h ratio) : Prop :=
  let scale := gridScale lp.buyingBudget ratio raw.2.2
  scale / 16 < Tolls.distanceTo G (fun v => lp.buying v + (scale / allowance raw.1) * lp.physical v)
    (lp.rowSource raw.2.1 raw.1) (lp.rowMate raw.2.1 raw.1)

abbrev FixedRow (allowance : Fin h → ℚ) (ratio : ℕ) :=
  {raw : RawRow h ratio // lp.IncludedRow allowance ratio raw}

instance fixedRowFintype (allowance : Fin h → ℚ) (ratio : ℕ) :
    Fintype (lp.FixedRow allowance ratio) := Fintype.ofFinite _

theorem gridScale_pos (budget_pos : 0 < lp.buyingBudget) (ratio : ℕ) (ratio_ge : 2 ≤ ratio) (depth : ℕ) :
    0 < gridScale lp.buyingBudget ratio depth := by
  have hr : (0 : ℚ) < ratio := by exact_mod_cast (show 0 < ratio by omega)
  unfold gridScale
  positivity

theorem endpoint_toll_mass (allowance scale : ℚ) (i : Fin h) (side : Bool)
    (scale_pos : 0 < scale) (allowance_pos : 0 < allowance)
    (length_bound : lp.fractionalLength i ≤ allowance / 64)
    (included : scale / 16 < Tolls.distanceTo G
      (fun v => lp.buying v + (scale / allowance) * lp.physical v)
      (lp.rowSource side i) (lp.rowMate side i)) :
    3 * (scale / 16) / 4 ≤ ∑ v, lp.opening v * Tolls.row G lp.buying lp.physical
      (scale / allowance) (scale / 16) (lp.rowSource side i) v := by
  cases side with
  | false =>
    exact Tolls.fractional_toll_mass G lp.buying lp.physical lp.opening scale allowance
      lp.buying_nonneg lp.physical_nonneg scale_pos allowance_pos (lp.source_buying i) (lp.source_physical i)
      (lp.flow i) (lp.flow_nonneg i) (lp.unit i) (lp.capacity i) included length_bound
  | true =>
    have length_rev : lp.reversed.fractionalLength i ≤ allowance / 64 := by simpa using length_bound
    exact Tolls.fractional_toll_mass G lp.reversed.buying lp.reversed.physical lp.reversed.opening scale allowance
      lp.reversed.buying_nonneg lp.reversed.physical_nonneg scale_pos allowance_pos
      (lp.reversed.source_buying i) (lp.reversed.source_physical i)
      (lp.reversed.flow i) (lp.reversed.flow_nonneg i) (lp.reversed.unit i) (lp.reversed.capacity i)
      included length_rev

def fixedTollData (allowance : Fin h → ℚ) (ratio : ℕ) (budget_pos : 0 < lp.buyingBudget)
    (ratio_ge : 2 ≤ ratio) (allowance_pos : ∀ i, 0 < allowance i)
    (length_bound : ∀ i, lp.fractionalLength i ≤ allowance i / 64) : Helper.TollData V (lp.FixedRow allowance ratio) where
  vertexOrder := (Finset.univ : Finset V).toList
  rowOrder := (Finset.univ : Finset (lp.FixedRow allowance ratio)).toList
  vertexOrder_nodup := Finset.univ.nodup_toList
  rowOrder_nodup := Finset.univ.nodup_toList
  vertexOrder_complete v := by simp
  rowOrder_complete r := by simp
  buying := lp.buying
  opening := lp.opening
  radius row := gridScale lp.buyingBudget ratio row.val.2.2 / 16
  toll row v := Tolls.row G lp.buying lp.physical
    (gridScale lp.buyingBudget ratio row.val.2.2 / allowance row.val.1)
    (gridScale lp.buyingBudget ratio row.val.2.2 / 16) (lp.rowSource row.val.2.1 row.val.1) v
  buying_nonneg := lp.buying_nonneg
  opening_nonneg v := (lp.opening_bounds v).1
  radius_pos row := by have hs := lp.gridScale_pos budget_pos ratio ratio_ge row.val.2.2; positivity
  toll_nonneg row v := Tolls.row_nonneg G _ _ _ _ _ _
  toll_le_buying row v := by
    have hs := lp.gridScale_pos budget_pos ratio ratio_ge row.val.2.2
    have hb := Tolls.row_bounds G lp.buying lp.physical
      (gridScale lp.buyingBudget ratio row.val.2.2 / allowance row.val.1)
      (gridScale lp.buyingBudget ratio row.val.2.2 / 16) lp.buying_nonneg lp.physical_nonneg
      (div_pos hs (allowance_pos row.val.1)).le (by positivity) (lp.rowSource row.val.2.1 row.val.1) v
    exact hb.2.trans (min_le_left _ _)
  toll_le_radius row v := by
    have hs := lp.gridScale_pos budget_pos ratio ratio_ge row.val.2.2
    have hb := Tolls.row_bounds G lp.buying lp.physical
      (gridScale lp.buyingBudget ratio row.val.2.2 / allowance row.val.1)
      (gridScale lp.buyingBudget ratio row.val.2.2 / 16) lp.buying_nonneg lp.physical_nonneg
      (div_pos hs (allowance_pos row.val.1)).le (by positivity) (lp.rowSource row.val.2.1 row.val.1) v
    exact hb.2.trans (min_le_right _ _)
  fractional_mass row := lp.endpoint_toll_mass (allowance row.val.1)
    (gridScale lp.buyingBudget ratio row.val.2.2) row.val.1 row.val.2.1
    (lp.gridScale_pos budget_pos ratio ratio_ge row.val.2.2) (allowance_pos row.val.1)
    (length_bound row.val.1) row.property

@[simp] theorem fixedTollData_budget (allowance : Fin h → ℚ) (ratio : ℕ)
    (budget_pos : 0 < lp.buyingBudget) (ratio_ge : 2 ≤ ratio)
    (allowance_pos : ∀ i, 0 < allowance i)
    (length_bound : ∀ i, lp.fractionalLength i ≤ allowance i / 64) :
    (lp.fixedTollData allowance ratio budget_pos ratio_ge allowance_pos length_bound).budget = lp.buyingBudget := rfl

theorem fixedRow_card_bound (allowance : Fin h → ℚ) (ratio : ℕ) (hh : 0 < h) (ratio_ge : 2 ≤ ratio) :
    Fintype.card (lp.FixedRow allowance ratio) ≤ (8 * h) ^ 2 := by
  calc
    _ ≤ Fintype.card (RawRow h ratio) := Fintype.card_subtype_le _
    _ = 2 * h * (gridDepth h ratio + 1) := by simp [RawRow]; ring
    _ ≤ _ := endpoint_scale_rows_bound h ratio hh ratio_ge

end BuyAtBulk.UpperBound.NodeLP
