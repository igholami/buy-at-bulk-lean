import BuyAtBulk.Computation.Runtime.Attachment

namespace BuyAtBulk.Computation.Runtime.StoredAttachment
open BuyAtBulk.UpperBound
variable {n : ℕ} (input : ShortestPath.GraphEncoding n)

def terminalBudget (n : ℕ) : ℕ :=
  2 * ((n + 1) * (4 * n + 2)) + 6 * (2 * n + 1) ^ 2 + 4 * n + 10

private theorem path_length {u v : Fin n} (path : input.graph.Path u v) : path.val.length ≤ n := by
  simpa using Nat.le_of_lt path.property.length_lt

theorem finishArm_count {s t z u : Fin n} (state : StoredState.State input.graph) (path : input.graph.Path z u) :
    (finishArm (s:=s) (t:=t) input state path).events.length ≤ terminalBudget n := by
  have bought := StoredState.purchase_count input.graph state path
  simp only [finishArm, List.length_append, List.length_cons, List.length_nil]
  unfold terminalBudget
  nlinarith

theorem finishComplete_count {s t z u : Fin n} (state : StoredState.State input.graph) (path : input.graph.Path s t) :
    (finishComplete (z:=z) (u:=u) input state path).events.length ≤ terminalBudget n := by
  have bought := StoredState.purchase_count input.graph state path
  simp only [finishComplete, List.length_append, List.length_cons, List.length_nil]
  unfold terminalBudget
  nlinarith

theorem birthArm_count {s t z u : Fin n} (state : StoredState.State input.graph)
    (path : input.graph.Path z u) (scale : ℚ) :
    (birthArm (s:=s) (t:=t) input state path scale).events.length ≤ terminalBudget n := by
  have bought := StoredState.purchase_count input.graph (StoredState.recordBirth input.graph state z scale).value path
  simp only [StoredState.recordBirth] at bought
  simp only [birthArm, List.length_append, StoredState.recordBirth, StoredState.recordEdge,
    List.length_cons, List.length_nil]
  unfold terminalBudget
  nlinarith

theorem joinEdge_count {s t z u v : Fin n} (state : StoredState.State input.graph)
    (inherited : input.graph.Path z u) (near : input.graph.Path z v) (scale : ℚ) :
    (joinEdge (s:=s) (t:=t) input state inherited near scale).events.length ≤ terminalBudget n := by
  have first := StoredState.purchase_count input.graph state inherited
  have second := StoredState.purchase_count input.graph (StoredState.purchase input.graph state inherited).value near
  have inherited_length := path_length input inherited
  have near_length := path_length input near
  have erased := Paths.toPath_count (Paths.append (Paths.reverse inherited.val).value near.val).value
  simp only [Paths.append_value, Paths.reverse_value, SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_reverse] at erased
  simp only [joinEdge, List.length_append, List.length_cons, List.length_nil,
    Paths.reverse_count, Paths.append_count, Paths.reverse_value, SimpleGraph.Walk.length_reverse,
    StoredState.recordEdge, Paths.append_value]
  unfold terminalBudget
  nlinarith

theorem joinArm_count {s t z u v : Fin n} (state : StoredState.State input.graph)
    (returned : input.graph.Path z v) (bypass : input.graph.Path u v) :
    (joinArm (s:=s) (t:=t) input state returned bypass).events.length ≤ terminalBudget n := by
  have returned_length := path_length input returned
  have bypass_length := path_length input bypass
  have erased := Paths.toPath_count (Paths.append returned.val (Paths.reverse bypass.val).value).value
  simp only [Paths.append_value, Paths.reverse_value, SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_reverse] at erased
  simp only [joinArm, List.length_append, List.length_cons, List.length_nil,
    Paths.reverse_count, Paths.append_count, Paths.append_value, Paths.reverse_value]
  unfold terminalBudget
  nlinarith

/-- One level pays all three queries, a full eligible-center scan, every
weight materialization, arithmetic/control overhead and terminal path work. -/
def stepBudget (n m : ℕ) : ℕ :=
  2 * AttachmentQueries.routeBudget n + m * (AttachmentQueries.routeBudget n + 10) +
    26 * n + 20 + terminalBudget n

theorem run_count (buying physical : Vector ℚ n) (allowance cutoff ratio threshold : ℚ) (s t : Fin n)
    (fuel : ℕ) (scale : ℚ) (z u : Fin n) (inherited : input.graph.Path z u) (state : StoredState.State input.graph) :
    (run input buying physical allowance cutoff ratio threshold s t fuel scale z u inherited state).events.length ≤
      (fuel + 1) * stepBudget n state.centers.length := by
  induction fuel generalizing scale z u inherited state with
  | zero =>
      have terminal := finishArm_count (s:=s) (t:=t) input state inherited
      simp only [run, List.length_cons]
      unfold stepBudget
      omega
  | succ k ih =>
      have reserve : stepBudget n state.centers.length ≤ (k + 1 + 1) * stepBudget n state.centers.length := by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right (stepBudget n state.centers.length)
          (show 1 ≤ k + 1 + 1 by omega)
      unfold stepBudget at reserve
      have terminal := finishArm_count (s:=s) (t:=t) input state inherited
      have weights := Weights.mixed_count buying physical state allowance scale
      have queried : (Queries.shortRoute input (Weights.mixed buying physical state allowance scale).value
          s t (ratDiv scale 16).value).events.length ≤ AttachmentQueries.routeBudget n :=
        Queries.shortRoute_count input _ s t _
      have near := AttachmentQueries.nearRecord_count input (Weights.mixed buying physical state allowance scale).value scale z state.centers
      simp only [run]
      split
      · simp only [List.length_append, List.length_cons, List.length_nil, Runtime.ratLe, Runtime.emit]
        unfold stepBudget
        omega
      · split
        · rename_i path found
          have done := finishComplete_count (z:=z) (u:=u) input state path
          simp only [List.length_append, List.length_cons, List.length_nil, Runtime.ratLe, Runtime.emit, Runtime.ratDiv_length]
          unfold stepBudget
          omega
        · split
          · have done := birthArm_count (s:=s) (t:=t) input state inherited scale
            simp only [List.length_append, List.length_cons, List.length_nil, Runtime.ratLe, Runtime.emit, Runtime.ratDiv_length]
            unfold stepBudget
            omega
          · rename_i v nearPath found
            have bought : (AttachmentQueries.boughtRoute input physical state u v threshold).events.length ≤
                AttachmentQueries.routeBudget n + 12 * n + 1 := by
              have actual := AttachmentQueries.boughtRoute_count input physical state u v threshold
              unfold AttachmentQueries.routeBudget
              omega
            split
            · have done := joinEdge_count (s:=s) (t:=t) input state inherited nearPath scale
              simp only [List.length_append, List.length_cons, List.length_nil, Runtime.ratLe, Runtime.emit, Runtime.ratDiv_length]
              unfold stepBudget
              omega
            · rename_i bypass returned
              have recursive := ih (ratDiv scale ratio).value z v nearPath state
              split
              · rename_i arm result
                have done := joinArm_count (s:=s) (t:=t) input
                  (run input buying physical allowance cutoff ratio threshold s t k (ratDiv scale ratio).value z v nearPath state).value.1 arm bypass
                simp only [List.length_append, List.length_cons, List.length_nil, Runtime.ratLe, Runtime.emit, Runtime.ratDiv_length]
                simp only [Nat.add_mul, Nat.one_mul] at *
                unfold stepBudget at *
                omega
              · simp only [List.length_append, List.length_cons, List.length_nil, Runtime.ratLe, Runtime.emit, Runtime.ratDiv_length]
                simp only [Nat.add_mul, Nat.one_mul] at *
                unfold stepBudget at *
                omega

end BuyAtBulk.Computation.Runtime.StoredAttachment
