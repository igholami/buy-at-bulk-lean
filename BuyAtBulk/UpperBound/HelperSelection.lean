import BuyAtBulk.UpperBound.HelperResult

/-! A proved helper selection independent of enumeration order. Packing uses
these three established helper properties, while executable construction can
supply any explicit complete node and row schedules. -/
noncomputable section
namespace BuyAtBulk.Helper
variable {V R : Type} [Fintype V] [Fintype R]
local instance helperSelectionDecEq : DecidableEq V := Classical.decEq _

structure Selection (D : TollData V R) (h : ℕ) where
  nodes : Finset V
  heavy_bought : D.heavy h ⊆ nodes
  buying_lt : (∑ v ∈ nodes, D.buying v) < 4 * TollData.alpha h * D.budget
  light_cover : ∀ r, D.lightRow h r → TollData.alpha h * D.radius r / 8 <
    ∑ v ∈ nodes \ D.heavy h, D.toll r v

namespace TollData
variable (D : TollData V R)

def canonicalSelection (h : ℕ) (hh : 0 < h) (budget_pos : 0 < D.budget)
    (row_count : Fintype.card R ≤ (8 * h) ^ 2) : Selection D h :=
  let cover := D.cover_fixed_tolls h hh budget_pos row_count
  ⟨D.helperSet h, cover.1, cover.2.1, cover.2.2⟩

/-- Construct a verified helper using supplied explicit finite schedules.
No equality with another schedule's selected set is asserted. -/
def selectionWithOrders (h : ℕ) (hh : 0 < h) (budget_pos : 0 < D.budget)
    (row_count : Fintype.card R ≤ (8 * h) ^ 2)
    (vertices : List V) (rows : List R) (vn : vertices.Nodup) (rn : rows.Nodup)
    (vc : ∀ v, v ∈ vertices) (rc : ∀ r, r ∈ rows) : Selection D h := by
  let ordered := D.withOrders vertices rows vn rn vc rc
  have cover := ordered.cover_fixed_tolls h hh budget_pos row_count
  exact ⟨ordered.helperSet h, cover.1, cover.2.1, cover.2.2⟩

@[simp] theorem selectionWithOrders_nodes (h : ℕ) (hh : 0 < h) (budget_pos : 0 < D.budget)
    (row_count : Fintype.card R ≤ (8 * h) ^ 2)
    (vertices : List V) (rows : List R) (vn : vertices.Nodup) (rn : rows.Nodup)
    (vc : ∀ v, v ∈ vertices) (rc : ∀ r, r ∈ rows) :
    (D.selectionWithOrders h hh budget_pos row_count vertices rows vn rn vc rc).nodes =
      (D.withOrders vertices rows vn rn vc rc).helperSet h := rfl

end TollData
end BuyAtBulk.Helper
