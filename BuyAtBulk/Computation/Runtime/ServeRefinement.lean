import BuyAtBulk.Computation.Runtime.Serve

set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.Computation.Runtime.StoredServe
open BuyAtBulk.UpperBound
variable {n : ℕ} (input : ShortestPath.GraphEncoding n)

private theorem mixedPath_value (buying physical : Vector ℚ n) (state : StoredState.State input.graph)
    (allowance scale : ℚ) (s t : Fin n) :
    (Queries.indexedPath input (Weights.mixed buying physical state allowance scale).value s t).value =
      ShortestPath.indexedPath input.graph
        (Attachment.mixedWeight input.graph (fun v => buying[v.val]) (fun v => physical[v.val])
          (StoredState.decode input.graph state) allowance scale) (Equiv.refl _) s t := by
  have weights : (fun v => (Weights.mixed buying physical state allowance scale).value[v.val]) =
      Attachment.mixedWeight input.graph (fun v => buying[v.val]) (fun v => physical[v.val])
        (StoredState.decode input.graph state) allowance scale := funext (Weights.mixed_get buying physical state allowance scale)
  simpa only [weights] using Queries.indexedPath_value input (Weights.mixed buying physical state allowance scale).value s t

def mainPhaseSpec (buying physical : Vector ℚ n) (budget allowance : ℚ) (h ratio : ℕ) (threshold : ℚ)
    (s t : Fin n) (main : input.graph.Path s t) (scale : ℚ) (state : RoundingState input.graph) :
    Option (RoundingState input.graph × input.graph.Path s t) :=
  if scale ≤ UpperBound.cutoff budget h ratio then some (Attachment.purchase input.graph state main, main) else
    let first := Serve.assignCenter input.graph (Equiv.refl _) (fun v => buying[v.val]) (fun v => physical[v.val]) allowance scale s state
    let second := Serve.assignCenter input.graph (Equiv.refl _) (fun v => buying[v.val]) (fun v => physical[v.val]) allowance scale t first.state
    if first.born || second.born then some (Serve.purchaseMain input.graph second.state first.arm main second.arm scale, main) else
      match Attachment.boughtRoute input.graph (Equiv.refl _) (fun v => physical[v.val]) second.state first.center second.center threshold with
      | none => some (Serve.purchaseMain input.graph second.state first.arm main second.arm scale, main)
      | some middle => some (Serve.reuseArms input.graph (Equiv.refl _) (fun v => buying[v.val]) (fun v => physical[v.val])
          budget allowance h ratio threshold scale s t first.center second.center first.arm second.arm middle second.state)

theorem mainPhase_value (buying physical : Vector ℚ n) (budget allowance : ℚ) (h ratio : ℕ) (threshold : ℚ)
    (s t : Fin n) (state : StoredState.State input.graph) (main : input.graph.Path s t) (scale : ℚ) (ratio_ge : 2 ≤ ratio) :
    decodeOption input (mainPhase input buying physical budget allowance h ratio threshold s t state main scale).value =
      mainPhaseSpec input buying physical budget allowance h ratio threshold s t main scale (StoredState.decode input.graph state) := by
  simp only [mainPhase, mainPhaseSpec, cutoff_value, ratLe, emit_value]
  by_cases cheap : scale ≤ UpperBound.cutoff budget h ratio
  · simp [cheap, decodeOption, decodeRoute, StoredState.decode_purchase]
  · simp only [cheap, decide_false, Bool.false_eq_true, ite_false]
    let first := assignCenter input buying physical allowance scale s state
    let second := assignCenter input buying physical allowance scale t first.value.state
    have first_eq := assignCenter_value input buying physical allowance scale s state
    rw [← first_eq]
    simp only [Assignment.decode]
    have second_eq := assignCenter_value input buying physical allowance scale t first.value.state
    rw [← second_eq]
    simp only [Assignment.decode]
    cases born : (first.value.born || second.value.born) with
    | true =>
        dsimp only [first, second] at born
        simp only [born, ite_true]
        simp [decodeOption, decodeRoute, purchaseMain_value, first, second]
    | false =>
        dsimp only [first, second] at born
        simp only [born, Bool.false_eq_true, ite_false]
        have middle_eq := AttachmentQueries.boughtRoute_value input physical second.value.state
          first.value.center second.value.center threshold
        rw [← middle_eq]
        cases middle : (AttachmentQueries.boughtRoute input physical second.value.state
            first.value.center second.value.center threshold).value with
        | none =>
            dsimp only [first, second] at middle
            simp [middle, decodeOption, decodeRoute, purchaseMain_value, first, second]
        | some path =>
            dsimp only [first, second] at middle
            simp only [middle, decodeOption, Option.map_some]
            simpa only [first, second] using congrArg some (reuseArms_value input buying physical budget allowance h ratio threshold scale
              s t first.value.center second.value.center first.value.arm second.value.arm path second.value.state ratio_ge)

/-- Stored Boolean-state execution returns exactly the existing deterministic
Serve result, including the actual selected main and inherited paths. -/
theorem run_value (buying physical : Vector ℚ n) (budget allowance : ℚ) (h ratio : ℕ) (threshold : ℚ)
    (s t : Fin n) (state : StoredState.State input.graph) (ratio_ge : 2 ≤ ratio) :
    decodeOption input (run input buying physical budget allowance h ratio threshold s t state).value =
      Serve.run input.graph (Equiv.refl _) (fun v => buying[v.val]) (fun v => physical[v.val])
        budget allowance h ratio threshold s t (StoredState.decode input.graph state) := by
  have early := AttachmentQueries.boughtRoute_value input physical state s t allowance
  simp only [run, Serve.run]
  rw [← early]
  cases route : (AttachmentQueries.boughtRoute input physical state s t allowance).value with
  | some path => simp [route, decodeOption, decodeRoute]
  | none =>
      simp only [route]
      rw [← selectScale_value input buying physical state budget allowance h ratio s t ratio_ge]
      cases selected : (selectScale input buying physical state budget allowance h ratio s t).value with
      | none =>
          simp only [selected, gridDepth_value h ratio ratio_ge, gridScale_value]
          rw [← mixedPath_value input buying physical state allowance (UpperBound.gridScale budget ratio (UpperBound.gridDepth h ratio)) s t]
          cases fallback : (Queries.indexedPath input
              (Weights.mixed buying physical state allowance (UpperBound.gridScale budget ratio (UpperBound.gridDepth h ratio))).value s t).value with
          | none => simp [fallback, decodeOption]
          | some path => simp [fallback, decodeOption, decodeRoute, StoredState.decode_purchase]
      | some d =>
          simp only [selected, emit_value, gridScale_value budget ratio (d - 1)]
          rw [← mixedPath_value input buying physical state allowance (UpperBound.gridScale budget ratio (d - 1)) s t]
          cases mainPath : (Queries.indexedPath input
              (Weights.mixed buying physical state allowance (UpperBound.gridScale budget ratio (d - 1))).value s t).value with
          | none => simp [mainPath, decodeOption]
          | some main =>
              simp only [mainPath]
              have actual := (mainPhase_value input buying physical budget allowance h ratio threshold s t state main
                (gridScale budget ratio d).value ratio_ge).trans
                (congrArg (fun q => mainPhaseSpec input buying physical budget allowance h ratio threshold s t main q
                  (StoredState.decode input.graph state)) (gridScale_value budget ratio d))
              refine actual.trans ?_
              simp only [mainPhaseSpec]
              split_ifs <;> first | rfl | (split <;> simp_all)


end BuyAtBulk.Computation.Runtime.StoredServe
