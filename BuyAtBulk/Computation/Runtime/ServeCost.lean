import BuyAtBulk.Computation.Runtime.Serve
import BuyAtBulk.Computation.Runtime.ServePathsCost

namespace BuyAtBulk.Computation.Runtime.StoredServe
open BuyAtBulk.UpperBound
variable {n : ℕ} (input : ShortestPath.GraphEncoding n)

private theorem bought_cap (physical : Vector ℚ n) (state : StoredState.State input.graph)
    (s t : Fin n) (threshold : ℚ) :
    (AttachmentQueries.boughtRoute input physical state s t threshold).events.length ≤
      AttachmentQueries.routeBudget n + 12 * n + 1 := by
  have actual := AttachmentQueries.boughtRoute_count input physical state s t threshold
  unfold AttachmentQueries.routeBudget
  omega

private theorem indexed_cap (weights : Vector ℚ n) (s t : Fin n) :
    (Queries.indexedPath input weights s t).events.length ≤ AttachmentQueries.routeBudget n := by
  have actual := Queries.indexedPath_count input weights s t
  unfold AttachmentQueries.routeBudget
  omega

def mainPhaseBudget (n h m : ℕ) : ℕ :=
  2 * (14 * n + (m + 1) * (AttachmentQueries.routeBudget n + 10) + 6) +
    (AttachmentQueries.routeBudget n + 12 * n + 1) + purchaseBudget n + reuseBudget n h (m + 2) + 20

theorem mainPhase_count (buying physical : Vector ℚ n) (budget allowance : ℚ) (h ratio : ℕ) (threshold : ℚ)
    (s t : Fin n) (state : StoredState.State input.graph) (main : input.graph.Path s t) (scale : ℚ) (ratio_ge : 2 ≤ ratio) :
    (mainPhase input buying physical budget allowance h ratio threshold s t state main scale).events.length ≤
      mainPhaseBudget n h state.centers.length := by
  let first := assignCenter input buying physical allowance scale s state
  let second := assignCenter input buying physical allowance scale t first.value.state
  have first_centers : first.value.state.centers.length ≤ state.centers.length + 1 :=
    assignCenter_centers input buying physical allowance scale s state
  have second_centers : second.value.state.centers.length ≤ first.value.state.centers.length + 1 :=
    assignCenter_centers input buying physical allowance scale t first.value.state
  have after_centers : second.value.state.centers.length ≤ state.centers.length + 2 := by omega
  let A := 14 * n + (state.centers.length + 1) * (AttachmentQueries.routeBudget n + 10) + 6
  have first_count : first.events.length ≤ A := by
    have actual := assignCenter_count input buying physical allowance scale s state
    have increasing := Nat.mul_le_mul_right (AttachmentQueries.routeBudget n + 10) (Nat.le_succ state.centers.length)
    simp only [Nat.succ_eq_add_one] at increasing
    dsimp [first, A]
    omega
  have second_count : second.events.length ≤ A := by
    have actual := assignCenter_count input buying physical allowance scale t first.value.state
    have increasing := Nat.mul_le_mul_right (AttachmentQueries.routeBudget n + 10) first_centers
    dsimp [second, A]
    omega
  have cheap := StoredState.purchase_count input.graph state main
  have purchased := purchaseMain_count input second.value.state first.value.arm main second.value.arm scale
  have middle := bought_cap input physical second.value.state first.value.center second.value.center threshold
  simp only [first, second] at first_count second_count purchased middle after_centers
  simp only [mainPhase]
  split
  · simp only [List.length_append, List.length_cons, List.length_nil, cutoff_count, ratLe, emit_length]
    unfold mainPhaseBudget purchaseBudget pathBudget
    nlinarith
  · split
    · simp only [List.length_append, List.length_cons, List.length_nil, cutoff_count, ratLe, emit_length, emit_value]
      unfold mainPhaseBudget
      dsimp [A] at *
      omega
    · split
      · simp only [List.length_append, List.length_cons, List.length_nil, cutoff_count, ratLe, emit_length, emit_value]
        unfold mainPhaseBudget
        dsimp [A] at *
        omega
      · rename_i path returned
        have reused := (reuseArms_count input buying physical budget allowance h ratio threshold scale
          s t first.value.center second.value.center first.value.arm second.value.arm path second.value.state ratio_ge).trans
          (reuseBudget_mono (n:=n) h after_centers)
        simp only [first, second] at reused
        simp only [List.length_append, List.length_cons, List.length_nil, cutoff_count, ratLe, emit_length, emit_value]
        unfold mainPhaseBudget
        dsimp [A] at *
        omega

def serveBudget (n h m : ℕ) : ℕ :=
  2 * AttachmentQueries.routeBudget n + 12 * n + 1 + selectionBudget n h +
    (10 * h + 12) + 2 * (4 * h + 8) + (14 * n + 1) + purchaseBudget n + mainPhaseBudget n h m + 20

/-- All emitted primitive operations, including early return, scalar/index
selection, center allocation and both possible attachments, are polynomial. -/
theorem run_count (buying physical : Vector ℚ n) (budget allowance : ℚ) (h ratio : ℕ) (threshold : ℚ)
    (s t : Fin n) (state : StoredState.State input.graph) (ratio_ge : 2 ≤ ratio) :
    (run input buying physical budget allowance h ratio threshold s t state).events.length ≤
      serveBudget n h state.centers.length := by
  have early := bought_cap input physical state s t allowance
  have selected := selectScale_count_uniform input buying physical state budget allowance h ratio s t ratio_ge
  have depth := gridDepth_count h ratio
  have Dbound := Runtime.gridDepth_bound h ratio ratio_ge
  simp only [run]
  split
  · simp only [List.length_append, List.length_cons, List.length_nil]
    unfold serveBudget
    omega
  · split
    · have scale : (gridScale budget ratio (gridDepth h ratio).value).events.length ≤ 4 * h + 8 := by
        rw [gridScale_count, gridDepth_value h ratio ratio_ge]
        omega
      have weights := Weights.mixed_count buying physical state allowance (gridScale budget ratio (gridDepth h ratio).value).value
      have queried := indexed_cap input (Weights.mixed buying physical state allowance (gridScale budget ratio (gridDepth h ratio).value).value).value s t
      split
      · simp only [List.length_append, List.length_cons, List.length_nil]
        unfold serveBudget
        omega
      · rename_i path returned
        have bought := StoredState.purchase_count input.graph state path
        simp only [List.length_append, List.length_cons, List.length_nil]
        unfold serveBudget purchaseBudget pathBudget
        nlinarith
    · rename_i d returned
      have range := selectScale_some_range input buying physical state budget allowance h ratio s t d ratio_ge returned
      have predecessor : (gridScale budget ratio (d - 1)).events.length ≤ 4 * h + 8 := by
        rw [gridScale_count]
        omega
      have scale : (gridScale budget ratio d).events.length ≤ 4 * h + 8 := by rw [gridScale_count]; omega
      have weights := Weights.mixed_count buying physical state allowance (gridScale budget ratio (d - 1)).value
      have queried := indexed_cap input (Weights.mixed buying physical state allowance (gridScale budget ratio (d - 1)).value).value s t
      simp only [emit_value]
      split
      · simp only [List.length_append, List.length_cons, List.length_nil, emit_length]
        unfold serveBudget
        omega
      · rename_i main returned
        have phase := mainPhase_count input buying physical budget allowance h ratio threshold s t state main (gridScale budget ratio d).value ratio_ge
        simp only [List.length_append, List.length_cons, List.length_nil, emit_length]
        unfold serveBudget
        omega

end BuyAtBulk.Computation.Runtime.StoredServe
