import BuyAtBulk.UpperBound.NodeLP

/-! Reversal of a node LP's actual graph paths, for toll rows at target endpoints. -/
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V]
local instance nodeLPReverseLocalInst1 : DecidableEq V := Classical.decEq V
local instance nodeLPReverseLocalInst2 (G : SimpleGraph V) : DecidableRel G.Adj := Classical.decRel _

/-- Reversal is a genuine bijection of all simple paths. -/
def pathReverseEquiv (G : SimpleGraph V) (s t : V) : G.Path s t ≃ G.Path t s where
  toFun := SimpleGraph.Path.reverse
  invFun := SimpleGraph.Path.reverse
  left_inv p := by apply Subtype.ext; exact SimpleGraph.Walk.reverse_reverse _
  right_inv p := by apply Subtype.ext; exact SimpleGraph.Walk.reverse_reverse _

theorem sum_reversed_paths (G : SimpleGraph V) {s t : V} (f : G.Path s t → ℚ) :
    (∑ p : G.Path t s, f p.reverse) = ∑ p : G.Path s t, f p :=
  (pathReverseEquiv G t s).sum_comp f

namespace NodeLP
variable {G : SimpleGraph V} {h : ℕ} (lp : NodeLP G h)

def reversed : NodeLP G h where
  source := lp.target
  target := lp.source
  buying := lp.buying
  physical := lp.physical
  demand := lp.demand
  opening := lp.opening
  flow i path := lp.flow i path.reverse
  buying_nonneg := lp.buying_nonneg
  physical_nonneg := lp.physical_nonneg
  demand_pos := lp.demand_pos
  opening_bounds := lp.opening_bounds
  flow_nonneg i path := lp.flow_nonneg i path.reverse
  unit i := by rw [sum_reversed_paths]; exact lp.unit i
  capacity i v := by
    have hs := sum_reversed_paths G (fun p : G.Path (lp.source i) (lp.target i) =>
      if v ∈ p.val.support then lp.flow i p else 0)
    simp only [SimpleGraph.Path.reverse, SimpleGraph.Walk.support_reverse, List.mem_reverse] at hs
    simpa only [SimpleGraph.Path.reverse] using hs.trans_le (lp.capacity i v)
  source_buying := lp.target_buying
  source_physical := lp.target_physical
  target_buying := lp.source_buying
  target_physical := lp.source_physical

@[simp] theorem reversed_buyingBudget : lp.reversed.buyingBudget = lp.buyingBudget := rfl

@[simp] theorem reversed_fractionalLength (i : Fin h) :
    lp.reversed.fractionalLength i = lp.fractionalLength i := by
  have hs := sum_reversed_paths G (fun p : G.Path (lp.source i) (lp.target i) =>
    NodeMetric.walkWeight G lp.physical p.val * lp.flow i p)
  simpa [fractionalLength, reversed, NodeMetric.walkWeight, SimpleGraph.Path.reverse,
    SimpleGraph.Walk.support_reverse] using hs

def oriented (side : Bool) : NodeLP G h := if side then lp.reversed else lp

@[simp] theorem oriented_fractionalLength (side : Bool) (i : Fin h) :
    (lp.oriented side).fractionalLength i = lp.fractionalLength i := by
  cases side <;> simp [oriented]

end NodeLP
end BuyAtBulk.UpperBound
