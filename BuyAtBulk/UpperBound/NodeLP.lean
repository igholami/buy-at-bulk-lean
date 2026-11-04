import BuyAtBulk.UpperBound.TollMass

/-! Natural affine LP on actual node-resource graph paths, used by the core
rounding run after the source node/edge subdivision and free-terminal reduction. -/
noncomputable section
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V]
local instance nodeLPLocalInst1 : DecidableEq V := Classical.decEq V
local instance nodeLPLocalInst2 (G : SimpleGraph V) : DecidableRel G.Adj := Classical.decRel _

structure NodeLP (G : SimpleGraph V) (h : ℕ) where
  source : Fin h → V
  target : Fin h → V
  buying : V → ℚ
  physical : V → ℚ
  demand : Fin h → ℚ
  opening : V → ℚ
  flow : ∀ i, G.Path (source i) (target i) → ℚ
  buying_nonneg : ∀ v, 0 ≤ buying v
  physical_nonneg : ∀ v, 0 ≤ physical v
  demand_pos : ∀ i, 0 < demand i
  opening_bounds : ∀ v, 0 ≤ opening v ∧ opening v ≤ 1
  flow_nonneg : ∀ i path, 0 ≤ flow i path
  unit : ∀ i, ∑ path, flow i path = 1
  capacity : ∀ i v, (∑ path, if v ∈ path.val.support then flow i path else 0) ≤ opening v
  source_buying : ∀ i, buying (source i) = 0
  source_physical : ∀ i, physical (source i) = 0
  target_buying : ∀ i, buying (target i) = 0
  target_physical : ∀ i, physical (target i) = 0

namespace NodeLP

variable {G : SimpleGraph V} {h : ℕ} (lp : NodeLP G h)

def buyingBudget : ℚ := ∑ v, lp.buying v * lp.opening v

def fractionalLength (i : Fin h) : ℚ :=
  ∑ path, NodeMetric.walkWeight G lp.physical path.val * lp.flow i path

def rentalBudget : ℚ := ∑ i, lp.demand i * lp.fractionalLength i

theorem buyingBudget_nonneg : 0 ≤ lp.buyingBudget :=
  Finset.sum_nonneg fun v _ => mul_nonneg (lp.buying_nonneg v) (lp.opening_bounds v).1

theorem fractionalLength_nonneg (i : Fin h) : 0 ≤ lp.fractionalLength i := by
  apply Finset.sum_nonneg
  intro path _
  apply mul_nonneg
  · exact Finset.sum_nonneg fun v _ => lp.physical_nonneg v
  · exact lp.flow_nonneg i path

theorem reachable (i : Fin h) : Nonempty (G.Path (lp.source i) (lp.target i)) := by
  by_contra hn
  have hempty : IsEmpty (G.Path (lp.source i) (lp.target i)) := ⟨fun path => hn ⟨path⟩⟩
  letI := hempty
  have unit := lp.unit i
  simp at unit

end NodeLP
end BuyAtBulk.UpperBound
