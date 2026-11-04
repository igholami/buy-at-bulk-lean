import BuyAtBulk.Computation.Runtime.AttachmentQueries
import BuyAtBulk.Computation.Runtime.Paths
import BuyAtBulk.Computation.Attachment.Algorithm

/-! Stored-state ConnectEndpoint. Bought cells are actual Boolean vectors;
all route, center, purchase and path-composition operations are traced. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.Computation.Runtime.StoredAttachment
open BuyAtBulk.UpperBound
open Rational
variable {n : ℕ} (input : ShortestPath.GraphEncoding n)

def decodeResult {s t z u : Fin n}
    (result : StoredState.State input.graph × AttachmentOutcome input.graph s t z u) :
    RoundingState input.graph × AttachmentOutcome input.graph s t z u :=
  (StoredState.decode input.graph result.1, result.2)

def finishArm {s t z u : Fin n} (state : StoredState.State input.graph) (path : input.graph.Path z u) :
    Traced (StoredState.State input.graph × AttachmentOutcome input.graph s t z u) :=
  let bought := StoredState.purchase input.graph state path
  ⟨(bought.value, .arm path), bought.events ++ [⟨.cons, [z.val.size, u.val.size]⟩]⟩

def finishComplete {s t z u : Fin n} (state : StoredState.State input.graph) (path : input.graph.Path s t) :
    Traced (StoredState.State input.graph × AttachmentOutcome input.graph s t z u) :=
  let bought := StoredState.purchase input.graph state path
  ⟨(bought.value, .completed path), bought.events ++ [⟨.cons, [s.val.size, t.val.size]⟩]⟩

def birthArm {s t z u : Fin n} (state : StoredState.State input.graph)
    (path : input.graph.Path z u) (scale : ℚ) :
    Traced (StoredState.State input.graph × AttachmentOutcome input.graph s t z u) :=
  let born := StoredState.recordBirth input.graph state z scale
  let bought := StoredState.purchase input.graph born.value path
  let edge := StoredState.recordEdge input.graph bought.value path scale
  ⟨(edge.value, .arm path), born.events ++ bought.events ++ edge.events ++ [⟨.cons, [z.val.size, u.val.size]⟩]⟩

def joinEdge {s t z u v : Fin n} (state : StoredState.State input.graph)
    (inherited : input.graph.Path z u) (near : input.graph.Path z v) (scale : ℚ) :
    Traced (StoredState.State input.graph × AttachmentOutcome input.graph s t z u) :=
  let boughtFirst := StoredState.purchase input.graph state inherited
  let boughtSecond := StoredState.purchase input.graph boughtFirst.value near
  let reversed := Paths.reverse inherited.val
  let joined := Paths.append reversed.value near.val
  let simple := Paths.toPath joined.value
  let edge := StoredState.recordEdge input.graph boughtSecond.value simple.value scale
  ⟨(edge.value, .arm inherited), boughtFirst.events ++ boughtSecond.events ++ reversed.events ++
    joined.events ++ simple.events ++ edge.events ++ [⟨.cons, [z.val.size, u.val.size]⟩]⟩

def joinArm {s t z u v : Fin n} (state : StoredState.State input.graph)
    (returned : input.graph.Path z v) (bypass : input.graph.Path u v) :
    Traced (StoredState.State input.graph × AttachmentOutcome input.graph s t z u) :=
  let reversed := Paths.reverse bypass.val
  let joined := Paths.append returned.val reversed.value
  let simple := Paths.toPath joined.value
  ⟨(state, .arm simple.value), reversed.events ++ joined.events ++ simple.events ++ [⟨.cons, [z.val.size, u.val.size]⟩]⟩

@[simp] theorem finishArm_value {s t z u : Fin n} (state : StoredState.State input.graph) (path : input.graph.Path z u) :
    decodeResult input (finishArm (s:=s) (t:=t) input state path).value =
      (Attachment.purchase input.graph (StoredState.decode input.graph state) path, .arm path) := by
  simp [decodeResult, finishArm, StoredState.decode_purchase]

@[simp] theorem finishComplete_value {s t z u : Fin n} (state : StoredState.State input.graph) (path : input.graph.Path s t) :
    decodeResult input (finishComplete (z:=z) (u:=u) input state path).value =
      (Attachment.purchase input.graph (StoredState.decode input.graph state) path, .completed path) := by
  simp [decodeResult, finishComplete, StoredState.decode_purchase]

@[simp] theorem birthArm_value {s t z u : Fin n} (state : StoredState.State input.graph)
    (path : input.graph.Path z u) (scale : ℚ) :
    decodeResult input (birthArm (s:=s) (t:=t) input state path scale).value =
      (UpperBound.recordEdge input.graph
        (Attachment.purchase input.graph (UpperBound.recordBirth input.graph (StoredState.decode input.graph state) z scale) path) path scale, .arm path) := by
  simp [decodeResult, birthArm, StoredState.decode_purchase]

@[simp] theorem joinEdge_value {s t z u v : Fin n} (state : StoredState.State input.graph)
    (inherited : input.graph.Path z u) (near : input.graph.Path z v) (scale : ℚ) :
    decodeResult input (joinEdge (s:=s) (t:=t) input state inherited near scale).value =
      (UpperBound.recordEdge input.graph
        (Attachment.purchase input.graph (Attachment.purchase input.graph (StoredState.decode input.graph state) inherited) near)
        (inherited.val.reverse.append near.val).toPath scale, .arm inherited) := by
  simp [decodeResult, joinEdge, StoredState.decode_purchase]

@[simp] theorem joinArm_value {s t z u v : Fin n} (state : StoredState.State input.graph)
    (returned : input.graph.Path z v) (bypass : input.graph.Path u v) :
    decodeResult input (joinArm (s:=s) (t:=t) input state returned bypass).value =
      (StoredState.decode input.graph state, .arm (returned.val.append bypass.reverse.val).toPath) := by
  simp [decodeResult, joinArm]

def run (buying physical : Vector ℚ n) (allowance cutoff ratio threshold : ℚ) (s t : Fin n) :
    (fuel : ℕ) → (scale : ℚ) → (z u : Fin n) → input.graph.Path z u → StoredState.State input.graph →
      Traced (StoredState.State input.graph × AttachmentOutcome input.graph s t z u)
  | 0, _, _, _, inherited, state =>
      let result := finishArm input state inherited
      ⟨result.value, ⟨.recurse, [0]⟩ :: result.events⟩
  | fuel + 1, scale, z, u, inherited, state =>
      let test := ratLe scale cutoff
      let control := [⟨Operation.recurse, [(fuel + 1).size]⟩] ++ test.events ++ [⟨.branch, [1]⟩]
      if test.value then
        let result := finishArm input state inherited
        ⟨result.value, control ++ result.events⟩
      else
        let weights := Weights.mixed buying physical state allowance scale
        let limit := ratDiv scale 16
        let route := Queries.shortRoute input weights.value s t limit.value
        let routeEvents := control ++ weights.events ++ limit.events ++ route.events ++ [⟨.branch, [1]⟩]
        match route.value with
        | some path =>
            let result := finishComplete input state path
            ⟨result.value, routeEvents ++ result.events⟩
        | none =>
            let nearby := AttachmentQueries.nearRecord input weights.value scale z state.centers
            let nearEvents := routeEvents ++ nearby.events ++ [⟨.branch, [1]⟩]
            match nearby.value with
            | none =>
                let result := birthArm input state inherited scale
                ⟨result.value, nearEvents ++ result.events⟩
            | some ⟨v, near⟩ =>
                let bypass := AttachmentQueries.boughtRoute input physical state u v threshold
                let bypassEvents := nearEvents ++ bypass.events ++ [⟨.branch, [1]⟩]
                match bypass.value with
                | none =>
                    let result := joinEdge input state inherited near scale
                    ⟨result.value, bypassEvents ++ result.events⟩
                | some bypass =>
                    let reduced := ratDiv scale ratio
                    let recursive := run buying physical allowance cutoff ratio threshold s t fuel reduced.value z v near state
                    let recursiveEvents := bypassEvents ++ reduced.events ++ recursive.events ++ [⟨.branch, [1]⟩]
                    match recursive.value.2 with
                    | .arm returned =>
                        let result := joinArm input recursive.value.1 returned bypass
                        ⟨result.value, recursiveEvents ++ result.events⟩
                    | .completed completed =>
                        ⟨(recursive.value.1, .completed completed), recursiveEvents ++ [⟨.cons, [s.val.size, t.val.size]⟩]⟩

/-- Every deterministic branch and actual returned path agrees with the
existing source program after decoding the stored Boolean purchases. -/
theorem run_value (buying physical : Vector ℚ n) (allowance cutoff ratio threshold : ℚ) (s t : Fin n)
    (fuel : ℕ) (scale : ℚ) (z u : Fin n) (inherited : input.graph.Path z u) (state : StoredState.State input.graph) :
    decodeResult input (run input buying physical allowance cutoff ratio threshold s t fuel scale z u inherited state).value =
      Attachment.run input.graph (Equiv.refl _) (fun v => buying[v.val]) (fun v => physical[v.val])
        allowance cutoff ratio threshold s t fuel scale z u inherited (StoredState.decode input.graph state) := by
  induction fuel generalizing scale z u inherited state with
  | zero => simpa only [run, Attachment.run] using finishArm_value input state inherited
  | succ k ih =>
      have weights : (fun v => (Weights.mixed buying physical state allowance scale).value[v.val]) =
          Attachment.mixedWeight input.graph (fun v => buying[v.val]) (fun v => physical[v.val])
            (StoredState.decode input.graph state) allowance scale :=
        funext (Weights.mixed_get buying physical state allowance scale)
      have centers : (StoredState.decode input.graph state).centers = state.centers := rfl
      have routed := Queries.shortRoute_value input (Weights.mixed buying physical state allowance scale).value s t (scale / 16)
      rw [weights] at routed
      have nearby := AttachmentQueries.nearRecord_value input (Weights.mixed buying physical state allowance scale).value scale z state.centers
      rw [weights] at nearby
      by_cases low : scale ≤ cutoff
      · simp only [run, Attachment.run, ratLe, emit_value, low, decide_true, ite_true]
        exact finishArm_value input state inherited
      · simp only [run, Attachment.run, ratLe, emit_value, low, decide_false, Bool.false_eq_true, ite_false, ratDiv_value, centers]
        rw [← routed]
        cases route : (Queries.shortRoute input (Weights.mixed buying physical state allowance scale).value s t (scale / 16)).value with
        | some path =>
            simpa only [route] using finishComplete_value input state path
        | none =>
            simp only [route]
            rw [← nearby]
            cases near : (AttachmentQueries.nearRecord input (Weights.mixed buying physical state allowance scale).value scale z state.centers).value with
            | none => simpa only [near] using birthArm_value input state inherited scale
            | some selected =>
                obtain ⟨v, nearPath⟩ := selected
                simp only [near]
                have bypassed := AttachmentQueries.boughtRoute_value input physical state u v threshold
                rw [← bypassed]
                cases bypass : (AttachmentQueries.boughtRoute input physical state u v threshold).value with
                | none => simpa only [bypass] using joinEdge_value input state inherited nearPath scale
                | some bypassPath =>
                    simp only [bypass]
                    rw [← ih (scale / ratio) z v nearPath state]
                    simp only [decodeResult]
                    cases result : (run input buying physical allowance cutoff ratio threshold s t k
                        (scale / ratio) z v nearPath state).value.2 with
                    | arm returned =>
                        simpa only [result, decodeResult] using
                          joinArm_value input (run input buying physical allowance cutoff ratio threshold s t k
                            (scale / ratio) z v nearPath state).value.1 returned bypassPath
                    | completed completed => simp only [result]

end BuyAtBulk.Computation.Runtime.StoredAttachment
