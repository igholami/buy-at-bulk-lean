import BuyAtBulk.Computation.Runtime.ServePaths

/-! Closed stored finite-data ServeDemandPair. All shortest paths, grid
choices, center searches, purchases and recursive attachments use the traced
implementations. The executable data never consults an LP flow. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.Computation.Runtime.StoredServe
open BuyAtBulk.UpperBound
variable {n : ℕ} (input : ShortestPath.GraphEncoding n)

def mainPhase (buying physical : Vector ℚ n) (budget allowance : ℚ) (h ratio : ℕ) (threshold : ℚ)
    (s t : Fin n) (state : StoredState.State input.graph) (main : input.graph.Path s t) (scale : ℚ) :
    Traced (Option (StoredState.State input.graph × input.graph.Path s t)) :=
  let cut := cutoff budget h ratio
  let cheap := ratLe scale cut.value
  let cheapEvents := cut.events ++ cheap.events ++ [⟨Operation.branch, [1]⟩]
  if cheap.value then
    let bought := StoredState.purchase input.graph state main
    ⟨some (bought.value, main), cheapEvents ++ bought.events ++ [⟨.cons, [s.val.size, t.val.size]⟩]⟩
  else
    let first := assignCenter input buying physical allowance scale s state
    let second := assignCenter input buying physical allowance scale t first.value.state
    let born := emit .branch [1, 1] (first.value.born || second.value.born)
    let assignedEvents := cheapEvents ++ first.events ++ second.events ++ born.events
    if born.value then
      let bought := purchaseMain input second.value.state first.value.arm main second.value.arm scale
      ⟨some (bought.value, main), assignedEvents ++ bought.events ++ [⟨.cons, [s.val.size, t.val.size]⟩]⟩
    else
      let middle := AttachmentQueries.boughtRoute input physical second.value.state first.value.center second.value.center threshold
      let middleEvents := assignedEvents ++ middle.events ++ [⟨.branch, [1]⟩]
      match middle.value with
      | none =>
          let bought := purchaseMain input second.value.state first.value.arm main second.value.arm scale
          ⟨some (bought.value, main), middleEvents ++ bought.events ++ [⟨.cons, [s.val.size, t.val.size]⟩]⟩
      | some path =>
          let reused := reuseArms input buying physical budget allowance h ratio threshold scale
            s t first.value.center second.value.center first.value.arm second.value.arm path second.value.state
          ⟨some reused.value, middleEvents ++ reused.events ++ [⟨.cons, [s.val.size, t.val.size]⟩]⟩

def run (buying physical : Vector ℚ n) (budget allowance : ℚ) (h ratio : ℕ) (threshold : ℚ)
    (s t : Fin n) (state : StoredState.State input.graph) :
    Traced (Option (StoredState.State input.graph × input.graph.Path s t)) :=
  let early := AttachmentQueries.boughtRoute input physical state s t allowance
  let earlyEvents := early.events ++ [⟨Operation.branch, [1]⟩]
  match early.value with
  | some route => ⟨some (state, route), earlyEvents ++ [⟨.cons, [s.val.size, t.val.size]⟩]⟩
  | none =>
      let selected := selectScale input buying physical state budget allowance h ratio s t
      let selectedEvents := earlyEvents ++ selected.events ++ [⟨.branch, [1]⟩]
      match selected.value with
      | none =>
          let depth := gridDepth h ratio
          let scale := gridScale budget ratio depth.value
          let weights := Weights.mixed buying physical state allowance scale.value
          let route := Queries.indexedPath input weights.value s t
          let routeEvents := selectedEvents ++ depth.events ++ scale.events ++ weights.events ++ route.events ++ [⟨.branch, [1]⟩]
          match route.value with
          | none => ⟨none, routeEvents⟩
          | some path =>
              let bought := StoredState.purchase input.graph state path
              ⟨some (bought.value, path), routeEvents ++ bought.events ++ [⟨.cons, [s.val.size, t.val.size]⟩]⟩
      | some d =>
          let previous := emit .natSub [d.size, 1, (d - 1).size] (d - 1)
          let predecessor := gridScale budget ratio previous.value
          let weights := Weights.mixed buying physical state allowance predecessor.value
          let route := Queries.indexedPath input weights.value s t
          let routeEvents := selectedEvents ++ previous.events ++ predecessor.events ++ weights.events ++ route.events ++ [⟨.branch, [1]⟩]
          match route.value with
          | none => ⟨none, routeEvents⟩
          | some main =>
              let scale := gridScale budget ratio d
              let phase := mainPhase input buying physical budget allowance h ratio threshold s t state main scale.value
              ⟨phase.value, routeEvents ++ scale.events ++ phase.events⟩

def decodeOption {s t : Fin n} (result : Option (StoredState.State input.graph × input.graph.Path s t)) :
    Option (RoundingState input.graph × input.graph.Path s t) := result.map (decodeRoute input)

end BuyAtBulk.Computation.Runtime.StoredServe
