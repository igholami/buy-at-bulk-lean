import BuyAtBulk.Computation.Runtime.ServeStorage
import BuyAtBulk.Computation.Runtime.ServeGridWords

/-! All newly recorded scales stay on the original finite geometric grid.
This gives one uniform bit invariant for an entire batch, rather than feeding
an inflated per-call bound back into each subsequent request. -/
namespace BuyAtBulk.Computation.Runtime.StoredServe
open BuyAtBulk.UpperBound
open Rational
variable {n : ℕ} (input : ShortestPath.GraphEncoding n)

theorem gridScale_div (budget : ℚ) (ratio depth : ℕ) :
    UpperBound.gridScale budget ratio depth / (ratio : ℚ) = UpperBound.gridScale budget ratio (depth + 1) := by
  simp only [UpperBound.gridScale, div_div, pow_succ]

theorem scaleAt_grid (budget : ℚ) (ratio d depth : ℕ) :
    StoredAttachment.scaleAt (UpperBound.gridScale budget ratio d / (ratio : ℚ)) (ratio : ℚ) depth =
      UpperBound.gridScale budget ratio (d + 1 + depth) := by
  induction depth with
  | zero => simp only [StoredAttachment.scaleAt, gridScale_div, Nat.add_zero]
  | succ k ih =>
      rw [StoredAttachment.scaleAt, ih, gridScale_div]
      congr 1

theorem purchaseMain_metadata (valid : ℚ → Prop) {s t u v : Fin n} (state : StoredState.State input.graph)
    (sarm : input.graph.Path s u) (main : input.graph.Path s t) (tarm : input.graph.Path t v) (scale : ℚ)
    (current : valid scale) (before : StoredAttachment.Metadata input valid state) :
    StoredAttachment.Metadata input valid (purchaseMain input state sarm main tarm scale).value := by
  simp only [StoredAttachment.Metadata, purchaseMain, StoredState.recordEdge,
    StoredState.purchase_centers, StoredState.purchase_edges, List.mem_cons]
  constructor
  · exact before.1
  · intro edge member
    rcases member with rfl | member
    · exact current
    · exact before.2 edge member

theorem reuseArms_metadata (valid : ℚ → Prop) (buying physical : Vector ℚ n)
    (budget allowance : ℚ) (h ratio : ℕ) (threshold scale : ℚ)
    (s t u v : Fin n) (sarm : input.graph.Path s u) (tarm : input.graph.Path t v)
    (middle : input.graph.Path u v) (state : StoredState.State input.graph) (ratio_ge : 2 ≤ ratio)
    (future : ∀ depth ≤ UpperBound.gridDepth h ratio,
      valid (StoredAttachment.scaleAt (scale / (ratio : ℚ)) (ratio : ℚ) depth))
    (before : StoredAttachment.Metadata input valid state) :
    StoredAttachment.Metadata input valid
      (reuseArms input buying physical budget allowance h ratio threshold scale s t u v sarm tarm middle state).value.1 := by
  let D := (gridDepth h ratio).value
  let cut := (cutoff budget h ratio).value
  let base := (ratCast ratio).value
  let lowered := (ratDiv scale base).value
  have schedule (depth : ℕ) (bounded : depth ≤ D) : valid (StoredAttachment.scaleAt lowered base depth) := by
    simpa only [lowered, base, ratDiv_value, ratCast, emit_value] using future depth (by
      simpa only [D, gridDepth_value h ratio ratio_ge] using bounded)
  let first := StoredAttachment.run input buying physical allowance cut base threshold s t D lowered s u sarm state
  have first_meta : StoredAttachment.Metadata input valid first.value.1 := by
    simpa only [first, StoredAttachment.scaleAt] using StoredAttachment.run_metadata input valid buying physical
      allowance cut base threshold lowered s t D schedule D 0 (by omega) s u sarm state before
  have second_meta : StoredAttachment.Metadata input valid
      (StoredAttachment.run input buying physical allowance cut base threshold s t D lowered t v tarm first.value.1).value.1 := by
    simpa only [StoredAttachment.scaleAt] using StoredAttachment.run_metadata input valid buying physical
      allowance cut base threshold lowered s t D schedule D 0 (by omega) t v tarm first.value.1 first_meta
  simp only [D, cut, base, lowered, first, ratCast, emit_value, ratDiv_value] at first_meta second_meta
  simp only [reuseArms, ratCast, emit_value, ratDiv_value]
  split
  · exact first_meta
  · split <;> exact second_meta

theorem mainPhase_metadata (valid : ℚ → Prop) (buying physical : Vector ℚ n)
    (budget allowance : ℚ) (h ratio : ℕ) (threshold : ℚ) (s t : Fin n)
    (state : StoredState.State input.graph) (main : input.graph.Path s t) (scale : ℚ) (ratio_ge : 2 ≤ ratio)
    (current : valid scale)
    (future : ∀ depth ≤ UpperBound.gridDepth h ratio,
      valid (StoredAttachment.scaleAt (scale / (ratio : ℚ)) (ratio : ℚ) depth))
    (before : StoredAttachment.Metadata input valid state) :
    StateProperty input (StoredAttachment.Metadata input valid)
      (mainPhase input buying physical budget allowance h ratio threshold s t state main scale).value := by
  let first := assignCenter input buying physical allowance scale s state
  let second := assignCenter input buying physical allowance scale t first.value.state
  have first_meta : StoredAttachment.Metadata input valid first.value.state :=
    ⟨assignCenter_metadata input valid buying physical allowance scale s state current before.1,
      by simpa only [first, assignCenter_edges] using before.2⟩
  have second_meta : StoredAttachment.Metadata input valid second.value.state :=
    ⟨assignCenter_metadata input valid buying physical allowance scale t first.value.state current first_meta.1,
      by simpa only [second, assignCenter_edges] using first_meta.2⟩
  have purchased := purchaseMain_metadata input valid second.value.state first.value.arm main second.value.arm scale current second_meta
  simp only [first, second] at purchased second_meta
  simp only [mainPhase]
  split
  · simpa only [StateProperty, StoredAttachment.Metadata, StoredState.purchase_centers, StoredState.purchase_edges] using before
  · split
    · exact purchased
    · split
      · exact purchased
      · rename_i path returned
        exact reuseArms_metadata input valid buying physical budget allowance h ratio threshold scale
          s t first.value.center second.value.center first.value.arm second.value.arm path second.value.state ratio_ge future second_meta

def metadataBudget (h L : ℕ) : ℕ := gridScalarBudget (4 * h + 3) (L + 4)

/-- Every retained record in every successful request remains within a
single budget derived from the original graph/LP metadata. -/
theorem run_metadata (buying physical : Vector ℚ n) (budget allowance : ℚ) (h ratio : ℕ) (threshold : ℚ)
    (s t : Fin n) (state : StoredState.State input.graph) (L : ℕ) (ratio_ge : 2 ≤ ratio)
    (budget_width : (Code.ofRat budget).bits ≤ L) (ratio_width : ratio.size ≤ L)
    (before : StoredAttachment.Metadata input (fun q => (Code.ofRat q).bits ≤ metadataBudget h L) state) :
    StateProperty input (StoredAttachment.Metadata input (fun q => (Code.ofRat q).bits ≤ metadataBudget h L))
      (run input buying physical budget allowance h ratio threshold s t state).value := by
  let valid := fun q => (Code.ofRat q).bits ≤ metadataBudget h L
  have Dbound := Runtime.gridDepth_bound h ratio ratio_ge
  have budget_input : (Code.ofRat budget).bits ≤ L + 4 := by omega
  have ratio_input : ratio.size ≤ L + 4 := by omega
  simp only [run]
  split
  · exact before
  · split
    · split
      · trivial
      · simpa only [StateProperty, StoredAttachment.Metadata, StoredState.purchase_centers, StoredState.purchase_edges] using before
    · rename_i d returned
      have range := selectScale_some_range input buying physical state budget allowance h ratio s t d ratio_ge returned
      simp only [emit_value]
      split
      · trivial
      · rename_i main returned
        have current : valid (gridScale budget ratio d).value := by
          rw [gridScale_value]
          exact gridScalarBudget_scale budget ratio d (4 * h + 3) (L + 4) budget_input ratio_input (by omega)
        have future (depth : ℕ) (bounded : depth ≤ UpperBound.gridDepth h ratio) :
            valid (StoredAttachment.scaleAt ((gridScale budget ratio d).value / (ratio : ℚ)) (ratio : ℚ) depth) := by
          rw [gridScale_value, scaleAt_grid]
          exact gridScalarBudget_scale budget ratio (d + 1 + depth) (4 * h + 3) (L + 4) budget_input ratio_input (by omega)
        exact mainPhase_metadata input valid buying physical budget allowance h ratio threshold s t state main
          (gridScale budget ratio d).value ratio_ge current future before

end BuyAtBulk.Computation.Runtime.StoredServe
