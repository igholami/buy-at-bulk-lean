import BuyAtBulk.Computation.Core.Initialization
import BuyAtBulk.UpperBound.FixedRows
import BuyAtBulk.UpperBound.HelperSelection

/-! The executable row schedules instantiate the proved helper theorem.
Selections made with different schedules are never identified. -/
noncomputable section
namespace BuyAtBulk.Computation.Core
open BuyAtBulk.UpperBound
variable {V : Type} [Fintype V] [DecidableEq V] {n h : ℕ} {G : SimpleGraph V} [DecidableRel G.Adj]
    (numbering : V ≃ Fin n) (lp : NodeLP G h)

def lpDatabase (allowance : Fin h → ℚ) (ratio : ℕ) : RowDatabase h ratio n :=
  materializeRows G numbering lp.buying lp.physical lp.buyingBudget allowance lp.source lp.target ratio

theorem database_included (allowance : Fin h → ℚ) (ratio : ℕ)
    (allowance_pos : ∀ i, 0 < allowance i) (raw : RawRow h ratio) :
    (getRow (lpDatabase numbering lp allowance ratio) raw).included = true ↔ lp.IncludedRow allowance ratio raw := by
  rw [lpDatabase, getRow_materializeRows]
  simpa only [NodeLP.IncludedRow, NodeLP.rowSource, NodeLP.rowMate, rowSource, rowMate] using
    materializeRow_included G numbering lp.buying lp.physical lp.buying_nonneg lp.physical_nonneg
      lp.buyingBudget lp.buyingBudget_nonneg allowance allowance_pos lp.source lp.target ratio raw

def semanticRows (allowance : Fin h → ℚ) (ratio : ℕ) (allowance_pos : ∀ i, 0 < allowance i) :
    List (lp.FixedRow allowance ratio) :=
  (includedRows (lpDatabase numbering lp allowance ratio)).attachWith (lp.IncludedRow allowance ratio)
    (fun raw member => (database_included numbering lp allowance ratio allowance_pos raw).mp
      ((mem_includedRows _ raw).mp member))

@[simp] theorem semanticRows_map_val (allowance : Fin h → ℚ) (ratio : ℕ)
    (allowance_pos : ∀ i, 0 < allowance i) :
    (semanticRows numbering lp allowance ratio allowance_pos).map Subtype.val =
      includedRows (lpDatabase numbering lp allowance ratio) := by
  exact List.attachWith_map_subtype_val _

theorem semanticRows_nodup (allowance : Fin h → ℚ) (ratio : ℕ)
    (allowance_pos : ∀ i, 0 < allowance i) :
    (semanticRows numbering lp allowance ratio allowance_pos).Nodup := by
  apply List.Nodup.of_map Subtype.val
  rw [semanticRows_map_val]
  exact includedRows_nodup _

theorem semanticRows_complete (allowance : Fin h → ℚ) (ratio : ℕ)
    (allowance_pos : ∀ i, 0 < allowance i) (row : lp.FixedRow allowance ratio) :
    row ∈ semanticRows numbering lp allowance ratio allowance_pos := by
  unfold semanticRows
  rw [List.mem_attachWith]
  exact (mem_includedRows _ row.val).mpr
    ((database_included numbering lp allowance ratio allowance_pos row.val).mpr row.property)

def orderedData (allowance : Fin h → ℚ) (ratio : ℕ) (budget_pos : 0 < lp.buyingBudget)
    (ratio_ge : 2 ≤ ratio) (allowance_pos : ∀ i, 0 < allowance i)
    (length_bound : ∀ i, lp.fractionalLength i ≤ allowance i / 64) : Helper.TollData V (lp.FixedRow allowance ratio) :=
  (lp.fixedTollData allowance ratio budget_pos ratio_ge allowance_pos length_bound).withOrders
    (vertexOrder numbering) (semanticRows numbering lp allowance ratio allowance_pos)
    (vertexOrder_nodup numbering) (semanticRows_nodup numbering lp allowance ratio allowance_pos)
    (mem_vertexOrder numbering) (semanticRows_complete numbering lp allowance ratio allowance_pos)

theorem database_toll (allowance : Fin h → ℚ) (ratio : ℕ) (allowance_pos : ∀ i, 0 < allowance i)
    (row : lp.FixedRow allowance ratio) (v : V) :
    storedToll numbering (lpDatabase numbering lp allowance ratio) row.val v =
      Tolls.row G lp.buying lp.physical
        (gridScale lp.buyingBudget ratio row.val.2.2 / allowance row.val.1)
        (gridScale lp.buyingBudget ratio row.val.2.2 / 16) (lp.rowSource row.val.2.1 row.val.1) v := by
  unfold storedToll lpDatabase
  rw [getRow_materializeRows]
  simpa only [NodeLP.rowSource, rowSource] using materializeRow_toll G numbering lp.buying lp.physical
    lp.buying_nonneg lp.physical_nonneg lp.buyingBudget lp.buyingBudget_nonneg allowance allowance_pos
    lp.source lp.target ratio row.val v

@[simp] theorem database_radius (allowance : Fin h → ℚ) (ratio : ℕ) (row : RawRow h ratio) :
    (getRow (lpDatabase numbering lp allowance ratio) row).radius = gridScale lp.buyingBudget ratio row.2.2 / 16 := by
  simp only [lpDatabase, getRow_materializeRows, materializeRow, rowFromDistances]

section Numeric
variable (allowance : Fin h → ℚ) (ratio : ℕ) (budget_pos : 0 < lp.buyingBudget)
    (ratio_ge : 2 ≤ ratio) (allowance_pos : ∀ i, 0 < allowance i)
    (length_bound : ∀ i, lp.fractionalLength i ≤ allowance i / 64)
local notation "D" => orderedData numbering lp allowance ratio budget_pos ratio_ge allowance_pos length_bound
local notation "db" => lpDatabase numbering lp allowance ratio

theorem heavyVertices_eq_data : (heavyVertices numbering lp.opening h).toFinset = (D).heavy h := by
  ext v
  simp only [List.mem_toFinset, mem_heavyVertices, Helper.TollData.heavy, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

theorem probability_eq_data : helperProbability lp.opening h = (D).probability h := by
  funext v
  simp only [helperProbability, Helper.TollData.probability, Helper.TollData.heavy,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

theorem toll_eq_data (row : lp.FixedRow allowance ratio) (v : V) :
    storedToll numbering db row.val v = (D).toll row v := by
  exact database_toll numbering lp allowance ratio allowance_pos row v

theorem radius_eq_data (row : lp.FixedRow allowance ratio) :
    (getRow db row.val).radius = (D).radius row := by
  exact database_radius numbering lp allowance ratio row.val

theorem factor_eq_data (row : lp.FixedRow allowance ratio) :
    helperFactor numbering db row.val = (D).factor row := by
  funext v
  simp only [helperFactor, Helper.TollData.factor]
  rw [toll_eq_data numbering lp allowance ratio budget_pos ratio_ge allowance_pos length_bound,
    radius_eq_data numbering lp allowance ratio budget_pos ratio_ge allowance_pos length_bound]

theorem amplitude_eq_data (row : lp.FixedRow allowance ratio) :
    helperAmplitude numbering lp.opening db row.val = (D).amplitude h row := by
  have heavy_sum : ((heavyVertices numbering lp.opening h).map fun v =>
        lp.opening v * storedToll numbering db row.val v).sum =
      ∑ v ∈ (D).heavy h, (D).opening v * (D).toll row v := by
    rw [← List.sum_toFinset _ (heavyVertices_nodup numbering lp.opening h),
      heavyVertices_eq_data numbering lp allowance ratio budget_pos ratio_ge allowance_pos length_bound]
    apply Finset.sum_congr rfl
    intro v _
    rw [toll_eq_data numbering lp allowance ratio budget_pos ratio_ge allowance_pos length_bound]
    rfl
  have light_iff : (((heavyVertices numbering lp.opening h).map fun v =>
      lp.opening v * storedToll numbering db row.val v).sum < 3 * (getRow db row.val).radius / 8) ↔
      (D).lightRow h row := by
    rw [heavy_sum, radius_eq_data numbering lp allowance ratio budget_pos ratio_ge allowance_pos length_bound]
    rfl
  by_cases light : (D).lightRow h row
  · simp only [helperAmplitude, Helper.TollData.amplitude, if_pos light, if_pos (light_iff.mpr light)]
    rfl
  · simp only [helperAmplitude, Helper.TollData.amplitude, if_neg light,
      if_neg (fun member => light (light_iff.mp member))]

theorem fixedCost_eq_data : helperFixedCost numbering lp.buying lp.opening h = (D).fixedCost h := by
  unfold helperFixedCost Helper.TollData.fixedCost
  rw [← List.sum_toFinset _ (heavyVertices_nodup numbering lp.opening h),
    heavyVertices_eq_data numbering lp allowance ratio budget_pos ratio_ge allowance_pos length_bound]
  rfl

theorem chooseHelper_eq_data :
    (chooseHelper numbering lp.buying lp.opening lp.buyingBudget db).1 = (D).selected h := by
  have factors : (fun row : lp.FixedRow allowance ratio => helperFactor numbering db row.val) = (D).factor := by
    funext row
    exact factor_eq_data numbering lp allowance ratio budget_pos ratio_ge allowance_pos length_bound row
  have amplitudes : (fun row : lp.FixedRow allowance ratio => helperAmplitude numbering lp.opening db row.val) = (D).amplitude h := by
    funext row
    exact amplitude_eq_data numbering lp allowance ratio budget_pos ratio_ge allowance_pos length_bound row
  unfold chooseHelper
  rw [← semanticRows_map_val numbering lp allowance ratio allowance_pos, chooseScheduled_mapRows]
  rw [factors, amplitudes,
    probability_eq_data numbering lp allowance ratio budget_pos ratio_ge allowance_pos length_bound,
    fixedCost_eq_data numbering lp allowance ratio budget_pos ratio_ge allowance_pos length_bound]
  rfl

theorem helperNodes_eq_data : helperNodes numbering lp.buying lp.opening lp.buyingBudget db = (D).helperSet h := by
  unfold helperNodes Helper.TollData.helperSet
  rw [heavyVertices_eq_data numbering lp allowance ratio budget_pos ratio_ge allowance_pos length_bound,
    chooseHelper_eq_data numbering lp allowance ratio budget_pos ratio_ge allowance_pos length_bound]
  ext v
  simp only [Finset.mem_union, List.mem_toFinset]

/-- The helper properties required by packing are proved for the exact set
returned by the executable, with its actual numbered schedules. -/
def computedSelection (hh : 0 < h) :
    Helper.Selection (lp.fixedTollData allowance ratio budget_pos ratio_ge allowance_pos length_bound) h := by
  have cover := (D).cover_fixed_tolls h hh budget_pos (lp.fixedRow_card_bound allowance ratio hh ratio_ge)
  have nodes := helperNodes_eq_data numbering lp allowance ratio budget_pos ratio_ge allowance_pos length_bound
  refine ⟨helperNodes numbering lp.buying lp.opening lp.buyingBudget db, ?_, ?_, ?_⟩
  · rw [nodes]
    exact cover.1
  · rw [nodes]
    exact cover.2.1
  · intro row light
    rw [nodes]
    exact cover.2.2 row light

@[simp] theorem computedSelection_nodes (hh : 0 < h) :
    (computedSelection numbering lp allowance ratio budget_pos ratio_ge allowance_pos length_bound hh).nodes =
      helperNodes numbering lp.buying lp.opening lp.buyingBudget db := rfl

end Numeric

end BuyAtBulk.Computation.Core
