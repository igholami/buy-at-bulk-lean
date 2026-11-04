import BuyAtBulk.UpperBound.ZeroLengthGraph
import BuyAtBulk.Model.FiniteFlowTransport

/-! Zero-length commodities retain precisely their original positive-flow
paths in the restricted graph. Fiber sums preserve unit flow and all node
marginals, including when multiple paths have the same restriction. -/
noncomputable section
namespace BuyAtBulk.UpperBound.NodeLP

variable {V : Type} [Fintype V] {G : SimpleGraph V} {h : ℕ}
local instance zeroLengthFlowLocalInst1 : DecidableEq V := Classical.decEq V
local instance zeroLengthFlowLocalInst2 (H : SimpleGraph V) : DecidableRel H.Adj := Classical.decRel _
variable (lp : NodeLP G h)

def raisedOpening (v : V) : ℚ := if lp.buying v = 0 then 1 else lp.opening v

theorem raisedOpening_bounds (v : V) : 0 ≤ lp.raisedOpening v ∧ lp.raisedOpening v ≤ 1 := by
  unfold raisedOpening
  split_ifs
  · norm_num
  · exact lp.opening_bounds v

theorem opening_le_raised (v : V) : lp.opening v ≤ lp.raisedOpening v := by
  unfold raisedOpening
  split_ifs
  · exact (lp.opening_bounds v).2
  · exact le_rfl

theorem raisedOpening_buyingBudget :
    (∑ v, lp.buying v * lp.raisedOpening v) = lp.buyingBudget := by
  apply Finset.sum_congr rfl
  intro v _
  by_cases zero : lp.buying v = 0 <;> simp [raisedOpening, zero]

def defaultZeroPath (i : Fin h) (zero_length : lp.fractionalLength i = 0) :
    (zeroGraph G lp.physical).Path (lp.source i) (lp.target i) :=
  restrictZeroPath G lp.physical (Classical.choose (lp.exists_positive_flow_path i))
    (lp.positive_path_zero_nodes i zero_length _ (Classical.choose_spec (lp.exists_positive_flow_path i)))

def zeroPathMap (i : Fin h) (zero_length : lp.fractionalLength i = 0)
    (path : G.Path (lp.source i) (lp.target i)) :
    (zeroGraph G lp.physical).Path (lp.source i) (lp.target i) :=
  if positive : 0 < lp.flow i path then
    restrictZeroPath G lp.physical path (lp.positive_path_zero_nodes i zero_length path positive)
  else lp.defaultZeroPath i zero_length

@[simp] theorem zeroPathMap_support (i : Fin h) (zero_length : lp.fractionalLength i = 0)
    (path : G.Path (lp.source i) (lp.target i)) (positive : 0 < lp.flow i path) :
    (lp.zeroPathMap i zero_length path).val.support = path.val.support := by
  simp only [zeroPathMap, dif_pos positive, restrictZeroPath_support]

def zeroFlow (i : Fin h) (zero_length : lp.fractionalLength i = 0) :
    (zeroGraph G lp.physical).Path (lp.source i) (lp.target i) → ℚ :=
  FiniteFlow.push (lp.zeroPathMap i zero_length) (lp.flow i)

theorem zeroFlow_nonneg (i : Fin h) (zero_length : lp.fractionalLength i = 0) (path) :
    0 ≤ lp.zeroFlow i zero_length path := by
  unfold zeroFlow FiniteFlow.push
  apply Finset.sum_nonneg
  intro p _
  split_ifs
  · exact lp.flow_nonneg i p
  · exact le_rfl

theorem zeroFlow_unit (i : Fin h) (zero_length : lp.fractionalLength i = 0) :
    (∑ path, lp.zeroFlow i zero_length path) = 1 := by
  have weighted := FiniteFlow.weighted_push (lp.zeroPathMap i zero_length) (lp.flow i) (fun _ => (1 : ℚ))
  simpa only [zeroFlow, one_mul, lp.unit i] using weighted

theorem zeroFlow_resource (i : Fin h) (zero_length : lp.fractionalLength i = 0) (v : V) :
    (∑ path, if v ∈ path.val.support then lp.zeroFlow i zero_length path else 0) =
      ∑ path, if v ∈ path.val.support then lp.flow i path else 0 := by
  have weighted := FiniteFlow.weighted_push (lp.zeroPathMap i zero_length) (lp.flow i)
    (fun path => if v ∈ path.val.support then (1 : ℚ) else 0)
  have same : (∑ path, (if v ∈ (lp.zeroPathMap i zero_length path).val.support then (1 : ℚ) else 0) * lp.flow i path) =
      ∑ path, if v ∈ path.val.support then lp.flow i path else 0 := by
    apply Finset.sum_congr rfl
    intro path _
    by_cases positive : 0 < lp.flow i path
    · rw [lp.zeroPathMap_support i zero_length path positive]
      split_ifs <;> simp
    · have hz : lp.flow i path = 0 := le_antisymm (not_lt.mp positive) (lp.flow_nonneg i path)
      simp [hz]
  simpa only [zeroFlow, ite_mul, one_mul, zero_mul] using weighted.trans same

end BuyAtBulk.UpperBound.NodeLP
