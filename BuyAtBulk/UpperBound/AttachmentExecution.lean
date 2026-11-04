import BuyAtBulk.UpperBound.ExecutionState

/-! Operational semantics of Algorithm `alg:attach`. Every guard is evaluated
on actual graph paths and actual bought resources. The natural-number index
bounds recursive skips; it is not a claimed running-time bound. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

def IsShortest {u v : V} (weight : V → ℚ) (path : G.Path u v) : Prop :=
  ∀ other : G.Path u v, NodeMetric.walkWeight G weight path.val ≤ NodeMetric.walkWeight G weight other.val

def HasShortMixedRoute (buying physical : V → ℚ) (state : RoundingState G)
    (allowance scale : ℚ) (s t : V) (threshold : ℚ) : Prop :=
  ∃ path : G.Path s t,
    NodeMetric.walkWeight G (mixedNodeWeight G buying physical state allowance scale) path.val ≤ threshold

inductive AttachmentOutcome (s t z u : V) where
  | arm (route : G.Path z u)
  | completed (route : G.Path s t)

/-- A shared guard for all non-base, non-completion attachment branches.
Both tests refer to the original request s,t, never to center pairs. -/
def AttachmentContinues (buying physical : V → ℚ) (state : RoundingState G)
    (allowance cutoff scale : ℚ) (s t : V) : Prop :=
  cutoff < scale ∧ ¬ HasShortMixedRoute G buying physical state allowance scale s t (scale / 16)

/-- Inference rules mirror the source's base/completion/birth/purchase/reuse
branches, including propagation of completion through pending recursive calls. -/
inductive AttachmentExec (buying physical : V → ℚ) (allowance cutoff ratio threshold : ℚ)
    (s t : V) : (fuel : ℕ) → (scale : ℚ) → (z u : V) → G.Path z u →
      RoundingState G → RoundingState G → AttachmentOutcome G s t z u → Prop where
  | base {fuel scale z u} (inherited : G.Path z u) (state : RoundingState G)
      (small : scale ≤ cutoff) :
      AttachmentExec buying physical allowance cutoff ratio threshold s t fuel scale z u inherited
        state (buyPath G state inherited) (.arm inherited)
  | complete {fuel scale z u} (inherited : G.Path z u) (state : RoundingState G)
      (above : cutoff < scale) (route : G.Path s t)
      (shortest : IsShortest G (mixedNodeWeight G buying physical state allowance scale) route)
      (short : NodeMetric.walkWeight G (mixedNodeWeight G buying physical state allowance scale)
        route.val ≤ scale / 16) :
      AttachmentExec buying physical allowance cutoff ratio threshold s t fuel scale z u inherited
        state (buyPath G state route) (.completed route)
  | birth {fuel scale z u} (inherited : G.Path z u) (state : RoundingState G)
      (continues : AttachmentContinues G buying physical state allowance cutoff scale s t)
      (separated : ¬ ∃ v, NearEligibleCenter G buying physical state allowance scale z v) :
      AttachmentExec buying physical allowance cutoff ratio threshold s t fuel scale z u inherited
        state (recordEdge G (buyPath G (recordBirth G state z scale) inherited) inherited scale)
        (.arm inherited)
  | purchase {fuel scale z u v} (inherited : G.Path z u) (near : G.Path z v)
      (state : RoundingState G)
      (continues : AttachmentContinues G buying physical state allowance cutoff scale s t)
      (eligible : EligibleCenter state.centers v scale)
      (shortest : IsShortest G (mixedNodeWeight G buying physical state allowance scale) near)
      (short : NodeMetric.walkWeight G (mixedNodeWeight G buying physical state allowance scale)
        near.val ≤ scale / 8)
      (no_bypass : ¬ HasShortBoughtRoute G physical state u v threshold) :
      AttachmentExec buying physical allowance cutoff ratio threshold s t fuel scale z u inherited
        state (recordEdge G (buyPath G (buyPath G state inherited) near)
          (inherited.val.reverse.append near.val).toPath scale) (.arm inherited)
  | reuse_arm {fuel scale z u v} (inherited : G.Path z u) (near : G.Path z v)
      (bypass : G.Path v u) (state final : RoundingState G) (returned : G.Path z v)
      (continues : AttachmentContinues G buying physical state allowance cutoff scale s t)
      (eligible : EligibleCenter state.centers v scale)
      (shortest : IsShortest G (mixedNodeWeight G buying physical state allowance scale) near)
      (short : NodeMetric.walkWeight G (mixedNodeWeight G buying physical state allowance scale)
        near.val ≤ scale / 8)
      (bypass_bought : bypass.val.support.toFinset ⊆ state.bought)
      (bypass_short : NodeMetric.walkWeight G physical bypass.val ≤ threshold)
      (recursive : AttachmentExec buying physical allowance cutoff ratio threshold s t fuel
        (scale / ratio) z v near state final (.arm returned)) :
      AttachmentExec buying physical allowance cutoff ratio threshold s t (fuel+1) scale z u inherited
        state final (.arm (returned.val.append bypass.val).toPath)
  | reuse_completed {fuel scale z u v} (inherited : G.Path z u) (near : G.Path z v)
      (bypass : G.Path v u) (state final : RoundingState G) (completed : G.Path s t)
      (continues : AttachmentContinues G buying physical state allowance cutoff scale s t)
      (eligible : EligibleCenter state.centers v scale)
      (shortest : IsShortest G (mixedNodeWeight G buying physical state allowance scale) near)
      (short : NodeMetric.walkWeight G (mixedNodeWeight G buying physical state allowance scale)
        near.val ≤ scale / 8)
      (bypass_bought : bypass.val.support.toFinset ⊆ state.bought)
      (bypass_short : NodeMetric.walkWeight G physical bypass.val ≤ threshold)
      (recursive : AttachmentExec buying physical allowance cutoff ratio threshold s t fuel
        (scale / ratio) z v near state final (.completed completed)) :
      AttachmentExec buying physical allowance cutoff ratio threshold s t (fuel+1) scale z u inherited
        state final (.completed completed)

end BuyAtBulk.UpperBound
