import BuyAtBulk.UpperBound.MainChoice
import BuyAtBulk.UpperBound.CenterAssignment
import BuyAtBulk.UpperBound.AttachmentInvariants

/-! Operational semantics of Algorithm `alg:main`, including early bought
reuse, empty-grid/cheap main branches, main purchases, two recursive arms,
and completion signals which end the entire original request. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

inductive ServeExec (buying physical : V → ℚ) (budget allowance : ℚ) (h ratio : ℕ)
    (threshold : ℚ) (s t : V) (reachable : Nonempty (G.Path s t)) :
    RoundingState G → RoundingState G → G.Path s t → Prop where
  | already_bought (state : RoundingState G) (route : G.Path s t)
      (shortest : IsShortestBought G physical state route)
      (short : NodeMetric.walkWeight G physical route.val ≤ allowance) :
      ServeExec buying physical budget allowance h ratio threshold s t reachable state state route
  | no_eligible (state : RoundingState G) (route : G.Path s t)
      (not_bought : ¬ HasShortBoughtRoute G physical state s t allowance)
      (empty : graphEligibleScales G buying physical state budget allowance h ratio s t reachable = ∅)
      (shortest : IsShortest G (mixedNodeWeight G buying physical state allowance
        (gridScale budget ratio (gridDepth h ratio))) route) :
      ServeExec buying physical budget allowance h ratio threshold s t reachable state (buyPath G state route) route
  | cheap (state : RoundingState G)
      (not_bought : ¬ HasShortBoughtRoute G physical state s t allowance)
      (choice : MainChoice G buying physical state budget allowance h ratio s t reachable)
      (small : gridScale budget ratio choice.index ≤ cutoff budget h ratio) :
      ServeExec buying physical budget allowance h ratio threshold s t reachable
        state (buyPath G state choice.mainPath) choice.mainPath
  | purchase (state first assigned : RoundingState G) (u v : V) (sarm : G.Path s u) (tarm : G.Path t v)
      (bornS bornT : Bool) (not_bought : ¬ HasShortBoughtRoute G physical state s t allowance)
      (choice : MainChoice G buying physical state budget allowance h ratio s t reachable)
      (above : cutoff budget h ratio < gridScale budget ratio choice.index)
      (assignS : CenterAssignment G buying physical allowance (gridScale budget ratio choice.index) s state first bornS u sarm)
      (assignT : CenterAssignment G buying physical allowance (gridScale budget ratio choice.index) t first assigned bornT v tarm)
      (must_buy : bornS = true ∨ bornT = true ∨ ¬ HasShortBoughtRoute G physical assigned u v threshold) :
      ServeExec buying physical budget allowance h ratio threshold s t reachable state
        (recordEdge G (buyPath G (buyPath G (buyPath G assigned sarm) choice.mainPath) tarm)
          ((sarm.val.reverse.append choice.mainPath.val).append tarm.val).toPath (gridScale budget ratio choice.index)) choice.mainPath
  | completed_first (state first assigned final : RoundingState G) (u v : V)
      (sarm : G.Path s u) (tarm : G.Path t v) (middle : G.Path u v) (completed : G.Path s t)
      (not_bought : ¬ HasShortBoughtRoute G physical state s t allowance)
      (choice : MainChoice G buying physical state budget allowance h ratio s t reachable)
      (above : cutoff budget h ratio < gridScale budget ratio choice.index)
      (assignS : CenterAssignment G buying physical allowance (gridScale budget ratio choice.index) s state first false u sarm)
      (assignT : CenterAssignment G buying physical allowance (gridScale budget ratio choice.index) t first assigned false v tarm)
      (middle_bought : middle.val.support.toFinset ⊆ assigned.bought)
      (middle_short : NodeMetric.walkWeight G physical middle.val ≤ threshold)
      (attachS : AttachmentExec G buying physical allowance (cutoff budget h ratio) ratio threshold s t
        (gridDepth h ratio) (gridScale budget ratio choice.index / ratio) s u sarm assigned final (.completed completed)) :
      ServeExec buying physical budget allowance h ratio threshold s t reachable state final completed
  | completed_second (state first assigned afterS final : RoundingState G) (u v : V)
      (sarm returnedS : G.Path s u) (tarm : G.Path t v) (middle : G.Path u v) (completed : G.Path s t)
      (not_bought : ¬ HasShortBoughtRoute G physical state s t allowance)
      (choice : MainChoice G buying physical state budget allowance h ratio s t reachable)
      (above : cutoff budget h ratio < gridScale budget ratio choice.index)
      (assignS : CenterAssignment G buying physical allowance (gridScale budget ratio choice.index) s state first false u sarm)
      (assignT : CenterAssignment G buying physical allowance (gridScale budget ratio choice.index) t first assigned false v tarm)
      (middle_bought : middle.val.support.toFinset ⊆ assigned.bought)
      (middle_short : NodeMetric.walkWeight G physical middle.val ≤ threshold)
      (attachS : AttachmentExec G buying physical allowance (cutoff budget h ratio) ratio threshold s t
        (gridDepth h ratio) (gridScale budget ratio choice.index / ratio) s u sarm assigned afterS (.arm returnedS))
      (attachT : AttachmentExec G buying physical allowance (cutoff budget h ratio) ratio threshold s t
        (gridDepth h ratio) (gridScale budget ratio choice.index / ratio) t v tarm afterS final (.completed completed)) :
      ServeExec buying physical budget allowance h ratio threshold s t reachable state final completed
  | reused (state first assigned afterS final : RoundingState G) (u v : V)
      (sarm returnedS : G.Path s u) (tarm returnedT : G.Path t v) (middle : G.Path u v)
      (not_bought : ¬ HasShortBoughtRoute G physical state s t allowance)
      (choice : MainChoice G buying physical state budget allowance h ratio s t reachable)
      (above : cutoff budget h ratio < gridScale budget ratio choice.index)
      (assignS : CenterAssignment G buying physical allowance (gridScale budget ratio choice.index) s state first false u sarm)
      (assignT : CenterAssignment G buying physical allowance (gridScale budget ratio choice.index) t first assigned false v tarm)
      (middle_bought : middle.val.support.toFinset ⊆ assigned.bought)
      (middle_short : NodeMetric.walkWeight G physical middle.val ≤ threshold)
      (attachS : AttachmentExec G buying physical allowance (cutoff budget h ratio) ratio threshold s t
        (gridDepth h ratio) (gridScale budget ratio choice.index / ratio) s u sarm assigned afterS (.arm returnedS))
      (attachT : AttachmentExec G buying physical allowance (cutoff budget h ratio) ratio threshold s t
        (gridDepth h ratio) (gridScale budget ratio choice.index / ratio) t v tarm afterS final (.arm returnedT)) :
      ServeExec buying physical budget allowance h ratio threshold s t reachable state final
        ((returnedS.val.append middle.val).append returnedT.val.reverse).toPath

end BuyAtBulk.UpperBound
