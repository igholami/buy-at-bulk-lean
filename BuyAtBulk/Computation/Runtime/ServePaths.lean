import BuyAtBulk.Computation.Runtime.ServeGrid
import BuyAtBulk.Computation.Runtime.ServeAssignment
import BuyAtBulk.Computation.Runtime.AttachmentStorage
import BuyAtBulk.Computation.Serve.Algorithm

namespace BuyAtBulk.Computation.Runtime.StoredServe
open BuyAtBulk.UpperBound
variable {n : ℕ} (input : ShortestPath.GraphEncoding n)

def decodeRoute {s t : Fin n} (result : StoredState.State input.graph × input.graph.Path s t) :
    RoundingState input.graph × input.graph.Path s t := (StoredState.decode input.graph result.1, result.2)

def purchaseMain {s t u v : Fin n} (state : StoredState.State input.graph)
    (sarm : input.graph.Path s u) (main : input.graph.Path s t) (tarm : input.graph.Path t v) (scale : ℚ) :
    Traced (StoredState.State input.graph) :=
  let first := StoredState.purchase input.graph state sarm
  let second := StoredState.purchase input.graph first.value main
  let third := StoredState.purchase input.graph second.value tarm
  let reversed := Paths.reverse sarm.val
  let left := Paths.append reversed.value main.val
  let right := Paths.append left.value tarm.val
  let simple := Paths.toPath right.value
  let edge := StoredState.recordEdge input.graph third.value simple.value scale
  ⟨edge.value, first.events ++ second.events ++ third.events ++ reversed.events ++ left.events ++ right.events ++ simple.events ++ edge.events⟩

@[simp] theorem purchaseMain_value {s t u v : Fin n} (state : StoredState.State input.graph)
    (sarm : input.graph.Path s u) (main : input.graph.Path s t) (tarm : input.graph.Path t v) (scale : ℚ) :
    StoredState.decode input.graph (purchaseMain input state sarm main tarm scale).value =
      Serve.purchaseMain input.graph (StoredState.decode input.graph state) sarm main tarm scale := by
  simp [purchaseMain, Serve.purchaseMain, StoredState.decode_purchase]

def joinRoutes {s t u v : Fin n} (sarm : input.graph.Path s u) (middle : input.graph.Path u v)
    (tarm : input.graph.Path t v) : Traced (input.graph.Path s t) :=
  let reversed := Paths.reverse tarm.val
  let left := Paths.append sarm.val middle.val
  let right := Paths.append left.value reversed.value
  let simple := Paths.toPath right.value
  ⟨simple.value, reversed.events ++ left.events ++ right.events ++ simple.events⟩

@[simp] theorem joinRoutes_value {s t u v : Fin n} (sarm : input.graph.Path s u)
    (middle : input.graph.Path u v) (tarm : input.graph.Path t v) :
    (joinRoutes input sarm middle tarm).value = ((sarm.val.append middle.val).append tarm.val.reverse).toPath := by
  simp [joinRoutes]

def cutoff (budget : ℚ) (h ratio : ℕ) : Traced ℚ := do
  let integer ← natMul ratio h
  let denominator ← ratCast integer
  ratDiv budget denominator

@[simp] theorem cutoff_value (budget : ℚ) (h ratio : ℕ) :
    (cutoff budget h ratio).value = UpperBound.cutoff budget h ratio := by
  simp [cutoff, Traced.bind_value, natMul, ratCast, emit_value, ratDiv_value, UpperBound.cutoff, Nat.cast_mul]

@[simp] theorem cutoff_count (budget : ℚ) (h ratio : ℕ) : (cutoff budget h ratio).events.length = 4 := rfl

def reuseArms (buying physical : Vector ℚ n) (budget allowance : ℚ) (h ratio : ℕ) (threshold scale : ℚ)
    (s t u v : Fin n) (sarm : input.graph.Path s u) (tarm : input.graph.Path t v)
    (middle : input.graph.Path u v) (state : StoredState.State input.graph) :
    Traced (StoredState.State input.graph × input.graph.Path s t) :=
  let depth := gridDepth h ratio
  let cut := cutoff budget h ratio
  let base := ratCast ratio
  let lowered := ratDiv scale base.value
  let header := depth.events ++ cut.events ++ base.events ++ lowered.events
  let first := StoredAttachment.run input buying physical allowance cut.value base.value threshold s t depth.value lowered.value s u sarm state
  let firstEvents := header ++ first.events ++ [⟨Operation.branch, [1]⟩]
  match first.value.2 with
  | .completed path => ⟨(first.value.1, path), firstEvents ++ [⟨.cons, [s.val.size, t.val.size]⟩]⟩
  | .arm returnedS =>
      let second := StoredAttachment.run input buying physical allowance cut.value base.value threshold s t depth.value lowered.value t v tarm first.value.1
      let secondEvents := firstEvents ++ second.events ++ [⟨.branch, [1]⟩]
      match second.value.2 with
      | .completed path => ⟨(second.value.1, path), secondEvents ++ [⟨.cons, [s.val.size, t.val.size]⟩]⟩
      | .arm returnedT =>
          let joined := joinRoutes input returnedS middle returnedT
          ⟨(second.value.1, joined.value), secondEvents ++ joined.events ++ [⟨.cons, [s.val.size, t.val.size]⟩]⟩

theorem reuseArms_value (buying physical : Vector ℚ n) (budget allowance : ℚ) (h ratio : ℕ) (threshold scale : ℚ)
    (s t u v : Fin n) (sarm : input.graph.Path s u) (tarm : input.graph.Path t v)
    (middle : input.graph.Path u v) (state : StoredState.State input.graph) (ratio_ge : 2 ≤ ratio) :
    decodeRoute input (reuseArms input buying physical budget allowance h ratio threshold scale s t u v sarm tarm middle state).value =
      Serve.reuseArms input.graph (Equiv.refl _) (fun v => buying[v.val]) (fun v => physical[v.val])
        budget allowance h ratio threshold scale s t u v sarm tarm middle (StoredState.decode input.graph state) := by
  have first := StoredAttachment.run_value input buying physical allowance (UpperBound.cutoff budget h ratio)
    ratio threshold s t (UpperBound.gridDepth h ratio) (scale / ratio) s u sarm state
  simp only [reuseArms, gridDepth_value h ratio ratio_ge, cutoff_value, ratCast, emit_value, ratDiv_value]
  unfold Serve.reuseArms
  rw [← first]
  simp only [StoredAttachment.decodeResult]
  cases returnedS : (StoredAttachment.run input buying physical allowance (UpperBound.cutoff budget h ratio)
      ratio threshold s t (UpperBound.gridDepth h ratio) (scale / ratio) s u sarm state).value.2 with
  | completed path => simp [returnedS, decodeRoute]
  | arm armS =>
      simp only [returnedS]
      let after := (StoredAttachment.run input buying physical allowance (UpperBound.cutoff budget h ratio)
        ratio threshold s t (UpperBound.gridDepth h ratio) (scale / ratio) s u sarm state).value.1
      have second := StoredAttachment.run_value input buying physical allowance (UpperBound.cutoff budget h ratio)
        ratio threshold s t (UpperBound.gridDepth h ratio) (scale / ratio) t v tarm after
      rw [← second]
      simp only [StoredAttachment.decodeResult]
      cases returnedT : (StoredAttachment.run input buying physical allowance (UpperBound.cutoff budget h ratio)
          ratio threshold s t (UpperBound.gridDepth h ratio) (scale / ratio) t v tarm after).value.2 with
      | completed path => simp [returnedT, decodeRoute, after]
      | arm armT => simp [returnedT, decodeRoute, joinRoutes_value, after]

end BuyAtBulk.Computation.Runtime.StoredServe
