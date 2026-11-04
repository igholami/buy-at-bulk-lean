import BuyAtBulk.Computation.ShortestPath
import BuyAtBulk.UpperBound.TollRows
import BuyAtBulk.UpperBound.FiniteGrid
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma

/-! Materialized fixed toll rows from original graph distances. Each original
endpoint/scale row computes one distance vector, then stores all n tolls. The
Boolean inclusion decision refers to the original mate before any purchases. -/
namespace BuyAtBulk.Computation.Core
open BuyAtBulk.UpperBound

abbrev RawRow (h ratio : ℕ) := Fin h × Bool × Fin (gridDepth h ratio + 1)

structure RowValues (n : ℕ) where
  radius : ℚ
  included : Bool
  toll : Vector ℚ n

abbrev RowDatabase (h ratio n : ℕ) := Vector (Vector (Vector (RowValues n) (gridDepth h ratio + 1)) 2) h

def boolIndex (side : Bool) : Fin 2 := if side then 1 else 0

def rowSource {V : Type} {h : ℕ} (source target : Fin h → V) (side : Bool) (i : Fin h) : V :=
  if side then target i else source i

def rowMate {V : Type} {h : ℕ} (source target : Fin h → V) (side : Bool) (i : Fin h) : V :=
  if side then source i else target i

def tollFromLabel (buying radius : ℚ) (label : WithTop ℚ) : ℚ :=
  if label = ⊤ then 0 else Tolls.toll buying radius (label.untopD 0)

variable {V : Type} [Fintype V] [DecidableEq V] {n h ratio : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

def rowFromDistances (buying : Fin n → ℚ) (radius : ℚ) (mate : Fin n)
    (distances : Vector (WithTop ℚ) n) : RowValues n :=
  { radius := radius
    included := decide (radius < (distances[mate.val]).untopD 0)
    toll := Vector.ofFn fun i => tollFromLabel (buying i) radius distances[i.val] }

@[simp] theorem rowFromDistances_toll (buying : Fin n → ℚ) (radius : ℚ) (mate vertex : Fin n)
    (distances : Vector (WithTop ℚ) n) :
    (rowFromDistances buying radius mate distances).toll[vertex.val] = tollFromLabel (buying vertex) radius distances[vertex.val] := by
  simp only [rowFromDistances, Vector.getElem_ofFn]

def materializeRow (buying physical : V → ℚ) (budget : ℚ) (allowance : Fin h → ℚ)
    (source target : Fin h → V) (ratio : ℕ) (raw : RawRow h ratio) : RowValues n :=
  let scale := gridScale budget ratio raw.2.2
  let weight := fun v => buying v + (scale / allowance raw.1) * physical v
  let distances := ShortestPath.indexedDistances G weight numbering (rowSource source target raw.2.1 raw.1)
  rowFromDistances (fun i => buying (numbering.symm i)) (scale / 16)
    (numbering (rowMate source target raw.2.1 raw.1)) distances

def materializeRows (buying physical : V → ℚ) (budget : ℚ) (allowance : Fin h → ℚ)
    (source target : Fin h → V) (ratio : ℕ) : RowDatabase h ratio n :=
  Vector.ofFn fun i => Vector.ofFn fun side => Vector.ofFn fun depth =>
    materializeRow G numbering buying physical budget allowance source target ratio (i, decide (side.val = 1), depth)

def getRow (database : RowDatabase h ratio n) (raw : RawRow h ratio) : RowValues n :=
  database[raw.1.val][(boolIndex raw.2.1).val][raw.2.2.val]

def rawRows (h ratio : ℕ) : List (RawRow h ratio) :=
  (List.finRange h).product ([false, true].product (List.finRange (gridDepth h ratio + 1)))

def includedRows (database : RowDatabase h ratio n) : List (RawRow h ratio) :=
  (rawRows h ratio).filter fun raw => (getRow database raw).included

@[simp] theorem getRow_materializeRows (buying physical : V → ℚ) (budget : ℚ) (allowance : Fin h → ℚ)
    (source target : Fin h → V) (ratio : ℕ) (raw : RawRow h ratio) :
    getRow (materializeRows G numbering buying physical budget allowance source target ratio) raw =
      materializeRow G numbering buying physical budget allowance source target ratio raw := by
  rcases raw with ⟨i, side, depth⟩
  cases side <;> simp [getRow, materializeRows, boolIndex]

@[simp] theorem mem_rawRows (ratio : ℕ) (raw : RawRow h ratio) : raw ∈ rawRows h ratio := by
  rcases raw with ⟨i, side, depth⟩
  cases side <;> simp [rawRows]

theorem rawRows_nodup (h ratio : ℕ) : (rawRows h ratio).Nodup := by
  apply List.Nodup.product (List.nodup_finRange h)
  exact List.Nodup.product (by simp) (List.nodup_finRange _)

theorem distance_reverse (weight : V → ℚ) (a b : V)
    (forward : Nonempty (G.Path a b)) (backward : Nonempty (G.Path b a)) :
    NodeMetric.distance G weight a b forward = NodeMetric.distance G weight b a backward := by
  apply le_antisymm
  · obtain ⟨path, cost⟩ := NodeMetric.exists_shortest G weight backward
    have bound := NodeMetric.distance_le_path G weight forward path.reverse
    have reversed : NodeMetric.walkWeight G weight path.reverse.val = NodeMetric.walkWeight G weight path.val := by
      simp only [NodeMetric.walkWeight, SimpleGraph.Path.reverse, SimpleGraph.Walk.support_reverse, List.toFinset_reverse]
    rw [reversed] at bound
    exact bound.trans_eq cost
  · obtain ⟨path, cost⟩ := NodeMetric.exists_shortest G weight forward
    have bound := NodeMetric.distance_le_path G weight backward path.reverse
    have reversed : NodeMetric.walkWeight G weight path.reverse.val = NodeMetric.walkWeight G weight path.val := by
      simp only [NodeMetric.walkWeight, SimpleGraph.Path.reverse, SimpleGraph.Walk.support_reverse, List.toFinset_reverse]
    rw [reversed] at bound
    exact bound.trans_eq cost

theorem indexedLabel_top_iff (weight : V → ℚ) (nonneg : ∀ v, 0 ≤ weight v) (source vertex : V) :
    (ShortestPath.indexedDistances G weight numbering source)[(numbering vertex).val] = ⊤ ↔
      ¬ Nonempty (G.Path source vertex) := by
  let input := ShortestPath.GraphEncoding.ofGraph G numbering
  let iso := ShortestPath.GraphEncoding.ofGraphIso G numbering
  have encoded := ShortestPath.shortestDistances_eq_top_iff input.graph (fun i => weight (numbering.symm i))
    (fun i => nonneg (numbering.symm i)) (numbering vertex) (numbering source)
  constructor
  · intro top reachable
    have reverse : Nonempty (G.Path vertex source) := ⟨reachable.some.reverse⟩
    have encoded_reachable : Nonempty (input.graph.Path (numbering vertex) (numbering source)) :=
      ⟨reverse.some.map iso.toHom iso.injective⟩
    exact encoded.mp top encoded_reachable
  · intro disconnected
    apply encoded.mpr
    intro reachable
    let back := ShortestPath.copyPath (reachable.some.map iso.symm.toHom iso.symm.injective)
      (iso.symm_apply_apply vertex) (iso.symm_apply_apply source)
    exact disconnected ⟨back.reverse⟩

theorem indexedLabel_eq (weight : V → ℚ) (nonneg : ∀ v, 0 ≤ weight v) (source vertex : V)
    (reachable : Nonempty (G.Path source vertex)) :
    (ShortestPath.indexedDistances G weight numbering source)[(numbering vertex).val] =
      (NodeMetric.distance G weight source vertex reachable : WithTop ℚ) := by
  have reverse : Nonempty (G.Path vertex source) := ⟨reachable.some.reverse⟩
  exact (ShortestPath.indexedDistances_correct G weight nonneg numbering vertex source reverse).trans
    (congrArg (fun q : ℚ => (q : WithTop ℚ)) (distance_reverse G weight vertex source reverse reachable))

theorem sourceDistance_eq (weight : V → ℚ) (nonneg : ∀ v, 0 ≤ weight v) (source vertex : V) :
    ((ShortestPath.indexedDistances G weight numbering source)[(numbering vertex).val]).untopD 0 =
      Tolls.distanceTo G weight source vertex := by
  classical
  by_cases reachable : Nonempty (G.Path source vertex)
  · rw [indexedLabel_eq G numbering weight nonneg source vertex reachable]
    simp only [WithTop.untopD_coe, Tolls.distanceTo_of_reachable G weight reachable]
  · rw [(indexedLabel_top_iff G numbering weight nonneg source vertex).mpr reachable]
    simp [Tolls.distanceTo, reachable]

theorem tollFromIndexedLabel_eq (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (coefficient radius : ℚ) (coefficient_nonneg : 0 ≤ coefficient) (source vertex : V) :
    tollFromLabel (buying vertex) radius
      (ShortestPath.indexedDistances G (fun v => buying v + coefficient * physical v) numbering source)[(numbering vertex).val] =
      Tolls.row G buying physical coefficient radius source vertex := by
  classical
  have nonneg : ∀ v, 0 ≤ buying v + coefficient * physical v :=
    fun v => add_nonneg (buying_nonneg v) (mul_nonneg coefficient_nonneg (physical_nonneg v))
  by_cases reachable : Nonempty (G.Path source vertex)
  · rw [indexedLabel_eq G numbering _ nonneg source vertex reachable]
    simp [tollFromLabel, Tolls.row, reachable]
  · rw [(indexedLabel_top_iff G numbering _ nonneg source vertex).mpr reachable]
    simp [tollFromLabel, Tolls.row, reachable]

theorem materializeRow_included (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (budget : ℚ) (budget_nonneg : 0 ≤ budget) (allowance : Fin h → ℚ) (allowance_pos : ∀ i, 0 < allowance i)
    (source target : Fin h → V) (ratio : ℕ) (raw : RawRow h ratio) :
    (materializeRow G numbering buying physical budget allowance source target ratio raw).included = true ↔
      gridScale budget ratio raw.2.2 / 16 < Tolls.distanceTo G
        (fun v => buying v + (gridScale budget ratio raw.2.2 / allowance raw.1) * physical v)
        (rowSource source target raw.2.1 raw.1) (rowMate source target raw.2.1 raw.1) := by
  have scale_nonneg : 0 ≤ gridScale budget ratio raw.2.2 := by unfold gridScale; positivity
  have nonneg : ∀ v, 0 ≤ buying v + (gridScale budget ratio raw.2.2 / allowance raw.1) * physical v :=
    fun v => add_nonneg (buying_nonneg v)
      (mul_nonneg (div_nonneg scale_nonneg (allowance_pos raw.1).le) (physical_nonneg v))
  simp only [materializeRow, rowFromDistances, decide_eq_true_eq]
  rw [sourceDistance_eq G numbering _ nonneg]

theorem materializeRow_toll (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (budget : ℚ) (budget_nonneg : 0 ≤ budget) (allowance : Fin h → ℚ) (allowance_pos : ∀ i, 0 < allowance i)
    (source target : Fin h → V) (ratio : ℕ) (raw : RawRow h ratio) (vertex : V) :
    (materializeRow G numbering buying physical budget allowance source target ratio raw).toll[(numbering vertex).val] =
      Tolls.row G buying physical (gridScale budget ratio raw.2.2 / allowance raw.1)
        (gridScale budget ratio raw.2.2 / 16) (rowSource source target raw.2.1 raw.1) vertex := by
  have scale_nonneg : 0 ≤ gridScale budget ratio raw.2.2 := by unfold gridScale; positivity
  unfold materializeRow
  rw [rowFromDistances_toll]
  simpa only [Equiv.symm_apply_apply] using
    tollFromIndexedLabel_eq G numbering buying physical buying_nonneg physical_nonneg _ _
      (div_nonneg scale_nonneg (allowance_pos raw.1).le) (rowSource source target raw.2.1 raw.1) vertex

@[simp] theorem mem_includedRows (database : RowDatabase h ratio n) (raw : RawRow h ratio) :
    raw ∈ includedRows database ↔ (getRow database raw).included = true := by
  simp only [includedRows, List.mem_filter, mem_rawRows, true_and, Bool.decide_eq_true]

theorem includedRows_nodup (database : RowDatabase h ratio n) : (includedRows database).Nodup :=
  (rawRows_nodup h ratio).filter _

theorem rawRows_length (h ratio : ℕ) : (rawRows h ratio).length = 2 * h * (gridDepth h ratio + 1) := by
  change ((List.finRange h) ×ˢ (([false, true] : List Bool) ×ˢ (List.finRange (gridDepth h ratio + 1)))).length = _
  rw [List.length_product, List.length_product]
  simp only [List.length_finRange, List.length_cons, List.length_nil]
  ring

end BuyAtBulk.Computation.Core
