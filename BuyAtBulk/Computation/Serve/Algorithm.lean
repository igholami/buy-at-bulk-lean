import BuyAtBulk.Computation.Serve.GridSearch
import BuyAtBulk.Computation.Serve.Assignment
import BuyAtBulk.UpperBound.ServeExecution

/-! Executable ServeDemandPair. Option.none records unreachable input; the
refinement theorem proves it cannot occur for the paper's feasible requests. -/
namespace BuyAtBulk.Computation.Serve
open BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

def purchaseMain {s t u v : V} (state : RoundingState G) (sarm : G.Path s u) (main : G.Path s t)
    (tarm : G.Path t v) (scale : ℚ) : RoundingState G :=
  recordEdge G (Attachment.purchase G (Attachment.purchase G (Attachment.purchase G state sarm) main) tarm)
    ((sarm.val.reverse.append main.val).append tarm.val).toPath scale

def reuseArms (buying physical : V → ℚ) (budget allowance : ℚ) (h ratio : ℕ) (threshold scale : ℚ)
    (s t u v : V) (sarm : G.Path s u) (tarm : G.Path t v) (middle : G.Path u v) (state : RoundingState G) :
    RoundingState G × G.Path s t :=
  let first := Attachment.run G numbering buying physical allowance (cutoff budget h ratio) ratio threshold s t
    (gridDepth h ratio) (scale / ratio) s u sarm state
  match first.2 with
  | .completed completed => (first.1, completed)
  | .arm returnedS =>
    let second := Attachment.run G numbering buying physical allowance (cutoff budget h ratio) ratio threshold s t
      (gridDepth h ratio) (scale / ratio) t v tarm first.1
    match second.2 with
    | .completed completed => (second.1, completed)
    | .arm returnedT => (second.1, ((returnedS.val.append middle.val).append returnedT.val.reverse).toPath)

def run (buying physical : V → ℚ) (budget allowance : ℚ) (h ratio : ℕ) (threshold : ℚ)
    (s t : V) (state : RoundingState G) : Option (RoundingState G × G.Path s t) :=
  match Attachment.boughtRoute G numbering physical state s t allowance with
  | some route => some (state, route)
  | none =>
    match selectScale G numbering buying physical state budget allowance h ratio s t with
    | none =>
      match ShortestPath.indexedPath G
          (Attachment.mixedWeight G buying physical state allowance (gridScale budget ratio (gridDepth h ratio))) numbering s t with
      | none => none
      | some route => some (Attachment.purchase G state route, route)
    | some d =>
      match ShortestPath.indexedPath G
          (Attachment.mixedWeight G buying physical state allowance (gridScale budget ratio (d - 1))) numbering s t with
      | none => none
      | some main =>
        let scale := gridScale budget ratio d
        if scale ≤ cutoff budget h ratio then some (Attachment.purchase G state main, main) else
          let first := assignCenter G numbering buying physical allowance scale s state
          let second := assignCenter G numbering buying physical allowance scale t first.state
          if first.born || second.born then
            some (purchaseMain G second.state first.arm main second.arm scale, main)
          else
            match Attachment.boughtRoute G numbering physical second.state first.center second.center threshold with
            | none => some (purchaseMain G second.state first.arm main second.arm scale, main)
            | some middle => some (reuseArms G numbering buying physical budget allowance h ratio threshold scale
                s t first.center second.center first.arm second.arm middle second.state)

end BuyAtBulk.Computation.Serve
