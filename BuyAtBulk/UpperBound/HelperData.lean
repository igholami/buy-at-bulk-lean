import BuyAtBulk.UpperBound.ConditionalExpectation
import BuyAtBulk.Computation.HelperChoose
import BuyAtBulk.UpperBound.FiniteGrid
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Finset.Dedup

/-! Heavy/light rows and the exact rational algorithm `CoverFixedTolls`.
The row hypotheses are precisely the conclusions of the toll-mass construction. -/
noncomputable section
namespace BuyAtBulk.Helper

variable (V R : Type) [Fintype V] [Fintype R]

structure TollData where
  buying : V → ℚ
  opening : V → ℚ
  radius : R → ℚ
  toll : R → V → ℚ
  vertexOrder : List V
  rowOrder : List R
  vertexOrder_nodup : vertexOrder.Nodup
  rowOrder_nodup : rowOrder.Nodup
  vertexOrder_complete : ∀ v, v ∈ vertexOrder
  rowOrder_complete : ∀ r, r ∈ rowOrder
  buying_nonneg : ∀ v, 0 ≤ buying v
  opening_nonneg : ∀ v, 0 ≤ opening v
  radius_pos : ∀ r, 0 < radius r
  toll_nonneg : ∀ r v, 0 ≤ toll r v
  toll_le_buying : ∀ r v, toll r v ≤ buying v
  toll_le_radius : ∀ r v, toll r v ≤ radius r
  fractional_mass : ∀ r, 3 * radius r / 4 ≤ ∑ v, opening v * toll r v

variable {V R}

namespace TollData

variable (D : TollData V R)
local instance helperDataOrderDecEqV : DecidableEq V := Classical.decEq V
local instance helperDataOrderDecEqR : DecidableEq R := Classical.decEq R

/-- Choose explicit complete schedules without changing any numeric row. -/
def withOrders (vertices : List V) (rows : List R) (vn : vertices.Nodup) (rn : rows.Nodup)
    (vc : ∀ v, v ∈ vertices) (rc : ∀ r, r ∈ rows) : TollData V R :=
  { D with
    vertexOrder := vertices
    rowOrder := rows
    vertexOrder_nodup := vn
    rowOrder_nodup := rn
    vertexOrder_complete := vc
    rowOrder_complete := rc }

theorem vertexOrder_toFinset : D.vertexOrder.toFinset = (Finset.univ : Finset V) := by
  classical
  ext v
  simp [D.vertexOrder_complete v]

theorem rowOrder_toFinset : D.rowOrder.toFinset = (Finset.univ : Finset R) := by
  classical
  ext r
  simp [D.rowOrder_complete r]

theorem vertexOrder_length : D.vertexOrder.length = Fintype.card V := by
  classical
  rw [← List.toFinset_card_of_nodup D.vertexOrder_nodup, D.vertexOrder_toFinset, Finset.card_univ]

theorem rowOrder_length : D.rowOrder.length = Fintype.card R := by
  classical
  rw [← List.toFinset_card_of_nodup D.rowOrder_nodup, D.rowOrder_toFinset, Finset.card_univ]

def budget : ℚ := ∑ v, D.buying v * D.opening v

def repetitions (h : ℕ) : ℕ := Nat.clog 2 (8 * h)
def alpha (h : ℕ) : ℚ := 128 * repetitions h

def heavy (h : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun v => 1 ≤ alpha h * D.opening v

def lightRow (h : ℕ) (r : R) : Prop :=
  (∑ v ∈ D.heavy h, D.opening v * D.toll r v) < 3 * D.radius r / 8

def probability (h : ℕ) (v : V) : ℚ := by
  classical
  exact if v ∈ D.heavy h then 0 else alpha h * D.opening v

def factor (r : R) (v : V) : ℚ := 1 - D.toll r v / (2 * D.radius r)

def amplitude (h : ℕ) (r : R) : ℚ := by
  classical
  exact if D.lightRow h r then 2 ^ (16 * repetitions h) else 0

def fixedCost (h : ℕ) : ℚ := ∑ v ∈ D.heavy h, D.buying v

def selected (h : ℕ) : List V :=
  (Computation.HelperExpressions.chooseScheduled D.buying (D.probability h) D.factor (D.amplitude h)
    (D.fixedCost h) (4 * alpha h * D.budget) D.rowOrder []
    D.vertexOrder).1

theorem selected_eq_choose (h : ℕ) : D.selected h =
    ConditionalExpectation.choose D.buying (D.probability h) D.factor (D.amplitude h)
      (D.fixedCost h) (4 * alpha h * D.budget) [] D.vertexOrder := by
  classical
  exact Computation.HelperExpressions.chooseScheduled_refines _ _ _ _ _ _ _
    D.rowOrder_nodup D.rowOrder_toFinset _ _

/-- Polynomial expression-work schedule of the actual helper selection.
The count includes expanded expression nodes and branch tests; operand bit
bounds are proved separately for the concrete estimator expressions. -/
theorem selected_work (h : ℕ) :
    (Computation.HelperExpressions.chooseScheduled D.buying (D.probability h) D.factor (D.amplitude h)
      (D.fixedCost h) (4 * alpha h * D.budget) D.rowOrder []
      D.vertexOrder).2 ≤
      Fintype.card V * (24 * (Fintype.card R + 1) * (Fintype.card V + 1) + 2) := by
  simpa only [List.length_nil, zero_add, D.vertexOrder_length, D.rowOrder_length] using Computation.HelperExpressions.chooseScheduled_work D.buying (D.probability h) D.factor
    (D.amplitude h) (D.fixedCost h) (4 * alpha h * D.budget) D.rowOrder []
    D.vertexOrder

def helperSet (h : ℕ) : Finset V := by
  classical
  exact D.heavy h ∪ (D.selected h).toFinset

omit [Fintype R] in
theorem probability_bounds (h : ℕ) (v : V) :
    0 ≤ D.probability h v ∧ D.probability h v ≤ 1 := by
  classical
  unfold probability
  split_ifs with hv
  · norm_num
  · have ha : 0 ≤ alpha h := by unfold alpha; positivity
    have not_heavy : ¬ 1 ≤ alpha h * D.opening v := by simpa [heavy] using hv
    exact ⟨mul_nonneg ha (D.opening_nonneg v), (not_le.mp not_heavy).le⟩

theorem selected_nodup (h : ℕ) : (D.selected h).Nodup := by
  rw [D.selected_eq_choose]
  apply ConditionalExpectation.choose_nodup
  simpa only [List.nil_append] using D.vertexOrder_nodup

theorem selected_not_heavy (h : ℕ) (v : V) (hv : v ∈ D.selected h) : v ∉ D.heavy h := by
  rw [D.selected_eq_choose] at hv
  classical
  intro hh
  have hz : D.probability h v = 0 := by simp [probability, hh]
  have he := ConditionalExpectation.choose_zero_probability D.buying (D.probability h)
    D.factor (D.amplitude h) (D.fixedCost h) (4 * alpha h * D.budget)
    D.vertexOrder [] v hz hv
  simp at he

theorem selected_potential_le (h : ℕ) :
    ConditionalExpectation.potential D.buying (D.probability h) D.factor (D.amplitude h)
      (D.fixedCost h) (4 * alpha h * D.budget) (D.selected h) [] ≤
    ConditionalExpectation.potential D.buying (D.probability h) D.factor (D.amplitude h)
      (D.fixedCost h) (4 * alpha h * D.budget) [] D.vertexOrder := by
  rw [D.selected_eq_choose]
  exact ConditionalExpectation.choose_potential_le _ _ _ _ _ _ (D.probability_bounds h) _ _

end TollData
end BuyAtBulk.Helper
