import BuyAtBulk.Computation.Runtime.ServePaths

namespace BuyAtBulk.Computation.Runtime.StoredServe
open BuyAtBulk.UpperBound
variable {n : ℕ} (input : ShortestPath.GraphEncoding n)

def pathBudget (n : ℕ) : ℕ := 6 * (3 * n + 1) ^ 2 + 10 * n + 10

def purchaseBudget (n : ℕ) : ℕ := 3 * ((n + 1) * (4 * n + 2)) + pathBudget n + 5

private theorem path_length {u v : Fin n} (path : input.graph.Path u v) : path.val.length ≤ n := by
  simpa using Nat.le_of_lt path.property.length_lt

theorem joinRoutes_count {s t u v : Fin n} (sarm : input.graph.Path s u)
    (middle : input.graph.Path u v) (tarm : input.graph.Path t v) :
    (joinRoutes input sarm middle tarm).events.length ≤ pathBudget n := by
  have sl := path_length input sarm
  have ml := path_length input middle
  have tl := path_length input tarm
  have erased := Paths.toPath_count
    (Paths.append (Paths.append sarm.val middle.val).value (Paths.reverse tarm.val).value).value
  simp only [Paths.append_value, Paths.reverse_value, SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_reverse] at erased
  simp only [joinRoutes, List.length_append, Paths.reverse_count, Paths.append_count,
    Paths.append_value, Paths.reverse_value, SimpleGraph.Walk.length_append]
  unfold pathBudget
  nlinarith

theorem purchaseMain_count {s t u v : Fin n} (state : StoredState.State input.graph)
    (sarm : input.graph.Path s u) (main : input.graph.Path s t) (tarm : input.graph.Path t v) (scale : ℚ) :
    (purchaseMain input state sarm main tarm scale).events.length ≤ purchaseBudget n := by
  have first := StoredState.purchase_count input.graph state sarm
  have second := StoredState.purchase_count input.graph (StoredState.purchase input.graph state sarm).value main
  have third := StoredState.purchase_count input.graph
    (StoredState.purchase input.graph (StoredState.purchase input.graph state sarm).value main).value tarm
  have sl := path_length input sarm
  have ml := path_length input main
  have tl := path_length input tarm
  have erased := Paths.toPath_count
    (Paths.append (Paths.append (Paths.reverse sarm.val).value main.val).value tarm.val).value
  simp only [Paths.append_value, Paths.reverse_value, SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_reverse] at erased
  simp only [purchaseMain, List.length_append, Paths.reverse_count, Paths.append_count,
    Paths.append_value, Paths.reverse_value, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
    StoredState.recordEdge, List.length_cons, List.length_nil]
  unfold purchaseBudget pathBudget
  nlinarith

theorem stepBudget_mono {m M : ℕ} (bound : m ≤ M) :
    StoredAttachment.stepBudget n m ≤ StoredAttachment.stepBudget n M := by
  have mul := Nat.mul_le_mul_right (AttachmentQueries.routeBudget n + 10) bound
  unfold StoredAttachment.stepBudget
  omega

def reuseBudget (n h m : ℕ) : ℕ :=
  10 * h + 30 + 2 * (2 * h + 2) * StoredAttachment.stepBudget n (m + 1) + pathBudget n

theorem reuseBudget_mono (h : ℕ) {m M : ℕ} (bound : m ≤ M) : reuseBudget n h m ≤ reuseBudget n h M := by
  have mul := Nat.mul_le_mul_left (2 * (2 * h + 2)) (stepBudget_mono (n:=n) (Nat.add_le_add_right bound 1))
  unfold reuseBudget
  omega

theorem reuseArms_count (buying physical : Vector ℚ n) (budget allowance : ℚ) (h ratio : ℕ) (threshold scale : ℚ)
    (s t u v : Fin n) (sarm : input.graph.Path s u) (tarm : input.graph.Path t v)
    (middle : input.graph.Path u v) (state : StoredState.State input.graph) (ratio_ge : 2 ≤ ratio) :
    (reuseArms input buying physical budget allowance h ratio threshold scale s t u v sarm tarm middle state).events.length ≤
      reuseBudget n h state.centers.length := by
  let D := (gridDepth h ratio).value
  let cut := (cutoff budget h ratio).value
  let base := (ratCast ratio).value
  let lowered := (ratDiv scale base).value
  let first := StoredAttachment.run input buying physical allowance cut base threshold s t D lowered s u sarm state
  have depth := gridDepth_count h ratio
  have Dbound : D ≤ 2 * h + 1 := by
    dsimp [D]
    rw [gridDepth_value h ratio ratio_ge]
    exact Runtime.gridDepth_bound h ratio ratio_ge
  have first_raw := StoredAttachment.run_count input buying physical allowance cut base threshold s t D lowered s u sarm state
  have first_count : first.events.length ≤ (2 * h + 2) * StoredAttachment.stepBudget n (state.centers.length + 1) :=
    first_raw.trans (Nat.mul_le_mul (by omega) (stepBudget_mono (Nat.le_succ _)))
  have storage := StoredAttachment.run_storage input buying physical allowance cut base threshold s t D lowered s u sarm state
  have centers : first.value.1.centers.length ≤ state.centers.length + 1 := storage.1
  have second_raw := StoredAttachment.run_count input buying physical allowance cut base threshold s t D lowered t v tarm first.value.1
  have second_count : (StoredAttachment.run input buying physical allowance cut base threshold s t D lowered t v tarm first.value.1).events.length ≤
      (2 * h + 2) * StoredAttachment.stepBudget n (state.centers.length + 1) :=
    second_raw.trans (Nat.mul_le_mul (by omega) (stepBudget_mono centers))
  simp only [D, cut, base, lowered, first, ratCast, emit_value, ratDiv_value] at first_count second_count
  simp only [reuseArms]
  split
  · simp only [List.length_append, List.length_cons, List.length_nil, cutoff_count, ratCast, emit_length, emit_value, ratDiv_value, ratDiv_length]
    unfold reuseBudget
    simp only [Nat.mul_assoc] at *
    omega
  · rename_i returnedS first_returned
    split
    · simp only [List.length_append, List.length_cons, List.length_nil, cutoff_count, ratCast, emit_length, emit_value, ratDiv_value, ratDiv_length]
      unfold reuseBudget
      simp only [Nat.mul_assoc] at *
      omega
    · rename_i returnedT second_returned
      have joined := joinRoutes_count input returnedS middle returnedT
      simp only [List.length_append, List.length_cons, List.length_nil, cutoff_count, ratCast, emit_length, emit_value, ratDiv_value, ratDiv_length]
      unfold reuseBudget
      simp only [Nat.mul_assoc] at *
      omega

end BuyAtBulk.Computation.Runtime.StoredServe
