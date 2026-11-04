import BuyAtBulk.Computation.Runtime.Serve

namespace BuyAtBulk.Computation.Runtime.StoredServe
open BuyAtBulk.UpperBound
variable {n : ℕ} (input : ShortestPath.GraphEncoding n)

def Growth (before : StoredState.State input.graph) (centers edges : ℕ) (after : StoredState.State input.graph) : Prop :=
  after.centers.length ≤ before.centers.length + centers ∧ after.edges.length ≤ before.edges.length + edges

def StateProperty {s t : Fin n} (property : StoredState.State input.graph → Prop) :
    Option (StoredState.State input.graph × input.graph.Path s t) → Prop
  | none => True
  | some result => property result.1

@[simp] theorem purchaseMain_centers {s t u v : Fin n} (state : StoredState.State input.graph)
    (sarm : input.graph.Path s u) (main : input.graph.Path s t) (tarm : input.graph.Path t v) (scale : ℚ) :
    (purchaseMain input state sarm main tarm scale).value.centers = state.centers := by
  simp [purchaseMain, StoredState.recordEdge]

@[simp] theorem purchaseMain_edges {s t u v : Fin n} (state : StoredState.State input.graph)
    (sarm : input.graph.Path s u) (main : input.graph.Path s t) (tarm : input.graph.Path t v) (scale : ℚ) :
    (purchaseMain input state sarm main tarm scale).value.edges.length = state.edges.length + 1 := by
  simp [purchaseMain, StoredState.recordEdge]

theorem reuseArms_growth (buying physical : Vector ℚ n) (budget allowance : ℚ) (h ratio : ℕ) (threshold scale : ℚ)
    (s t u v : Fin n) (sarm : input.graph.Path s u) (tarm : input.graph.Path t v)
    (middle : input.graph.Path u v) (state : StoredState.State input.graph) :
    Growth input state 2 2
      (reuseArms input buying physical budget allowance h ratio threshold scale s t u v sarm tarm middle state).value.1 := by
  let D := (gridDepth h ratio).value
  let cut := (cutoff budget h ratio).value
  let base := (ratCast ratio).value
  let lowered := (ratDiv scale base).value
  let first := StoredAttachment.run input buying physical allowance cut base threshold s t D lowered s u sarm state
  have fg := StoredAttachment.run_storage input buying physical allowance cut base threshold s t D lowered s u sarm state
  have fc : first.value.1.centers.length ≤ state.centers.length + 1 := fg.1
  have fe : first.value.1.edges.length ≤ state.edges.length + 1 := fg.2
  have sg := StoredAttachment.run_storage input buying physical allowance cut base threshold s t D lowered t v tarm first.value.1
  have sc : (StoredAttachment.run input buying physical allowance cut base threshold s t D lowered t v tarm first.value.1).value.1.centers.length ≤ state.centers.length + 2 := by
    have next := sg.1; omega
  have se : (StoredAttachment.run input buying physical allowance cut base threshold s t D lowered t v tarm first.value.1).value.1.edges.length ≤ state.edges.length + 2 := by
    have next := sg.2; omega
  simp only [D, cut, base, lowered, first, ratCast, emit_value, ratDiv_value] at fc fe sc se
  simp only [reuseArms, ratCast, emit_value, ratDiv_value]
  split
  · simp only [Growth]; constructor <;> omega
  · split <;> exact And.intro sc se

theorem mainPhase_growth (buying physical : Vector ℚ n) (budget allowance : ℚ) (h ratio : ℕ) (threshold : ℚ)
    (s t : Fin n) (state : StoredState.State input.graph) (main : input.graph.Path s t) (scale : ℚ) :
    StateProperty input (Growth input state 4 2)
      (mainPhase input buying physical budget allowance h ratio threshold s t state main scale).value := by
  let first := assignCenter input buying physical allowance scale s state
  let second := assignCenter input buying physical allowance scale t first.value.state
  have fc : first.value.state.centers.length ≤ state.centers.length + 1 :=
    assignCenter_centers input buying physical allowance scale s state
  have sc : second.value.state.centers.length ≤ first.value.state.centers.length + 1 :=
    assignCenter_centers input buying physical allowance scale t first.value.state
  have centers : second.value.state.centers.length ≤ state.centers.length + 2 := by omega
  have edges : second.value.state.edges.length = state.edges.length := by simp [first, second]
  simp only [first, second] at centers edges
  simp only [mainPhase]
  split
  · simp [StateProperty, Growth]
  · split
    · simp only [StateProperty, Growth, purchaseMain_centers, purchaseMain_edges]
      constructor <;> omega
    · split
      · simp only [StateProperty, Growth, purchaseMain_centers, purchaseMain_edges]
        constructor <;> omega
      · rename_i path returned
        have reused := reuseArms_growth input buying physical budget allowance h ratio threshold scale s t
          first.value.center second.value.center first.value.arm second.value.arm path second.value.state
        have rc := reused.1
        have re := reused.2
        simp only [first, second] at rc re
        simp only [StateProperty, Growth]
        constructor <;> omega

/-- Every successful request creates at most four center records and two
paid-edge records. This coarse bound is independent of rational magnitudes. -/
theorem run_growth (buying physical : Vector ℚ n) (budget allowance : ℚ) (h ratio : ℕ) (threshold : ℚ)
    (s t : Fin n) (state : StoredState.State input.graph) :
    StateProperty input (Growth input state 4 2)
      (run input buying physical budget allowance h ratio threshold s t state).value := by
  simp only [run]
  split
  · simp [StateProperty, Growth]
  · split
    · split
      · trivial
      · simp [StateProperty, Growth]
    · split
      · trivial
      · rename_i main returned
        exact mainPhase_growth input buying physical budget allowance h ratio threshold s t state main _

end BuyAtBulk.Computation.Runtime.StoredServe
