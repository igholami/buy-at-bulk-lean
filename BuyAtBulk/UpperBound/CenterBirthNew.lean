import BuyAtBulk.UpperBound.ExecutionState

/-! A separated free original endpoint cannot already be eligible at its
birth scale: its actual nil path would be a zero-cost nearby-center arm. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

theorem separated_center_new (buying physical : V → ℚ) (state : RoundingState G)
    (allowance scale : ℚ) (z : V) (terminal_buying : buying z = 0) (terminal_physical : physical z = 0)
    (scale_nonneg : 0 ≤ scale)
    (separated : ¬ ∃ center, NearEligibleCenter G buying physical state allowance scale z center) :
    ¬ EligibleCenter state.centers z scale := by
  intro eligible
  apply separated
  refine ⟨z, eligible, SimpleGraph.Path.nil, ?_⟩
  simp [NodeMetric.walkWeight, SimpleGraph.Path.nil, mixedNodeWeight, terminal_buying, terminal_physical,
    div_nonneg scale_nonneg (by norm_num : (0:ℚ) ≤ 8)]

end BuyAtBulk.UpperBound
