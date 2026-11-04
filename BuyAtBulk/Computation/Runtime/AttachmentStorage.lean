import BuyAtBulk.Computation.Runtime.AttachmentWords

namespace BuyAtBulk.Computation.Runtime.StoredAttachment
open BuyAtBulk.UpperBound
variable {n : ℕ} (input : ShortestPath.GraphEncoding n)

def StorageGrowth (before after : StoredState.State input.graph) : Prop :=
  after.centers.length ≤ before.centers.length + 1 ∧ after.edges.length ≤ before.edges.length + 1

def Metadata (valid : ℚ → Prop) (state : StoredState.State input.graph) : Prop :=
  (∀ record ∈ state.centers, valid record.birthScale) ∧ (∀ edge ∈ state.edges, valid edge.scale)

private theorem finishArm_storage {s t z u : Fin n} (state : StoredState.State input.graph) (path : input.graph.Path z u) :
    StorageGrowth input state (finishArm (s:=s) (t:=t) input state path).value.1 := by
  simp [StorageGrowth, finishArm]

private theorem finishComplete_storage {s t z u : Fin n} (state : StoredState.State input.graph) (path : input.graph.Path s t) :
    StorageGrowth input state (finishComplete (z:=z) (u:=u) input state path).value.1 := by
  simp [StorageGrowth, finishComplete]

private theorem birthArm_storage {s t z u : Fin n} (state : StoredState.State input.graph) (path : input.graph.Path z u) (scale : ℚ) :
    StorageGrowth input state (birthArm (s:=s) (t:=t) input state path scale).value.1 := by
  simp [StorageGrowth, birthArm, StoredState.recordBirth, StoredState.recordEdge]

private theorem joinEdge_storage {s t z u v : Fin n} (state : StoredState.State input.graph)
    (inherited : input.graph.Path z u) (near : input.graph.Path z v) (scale : ℚ) :
    StorageGrowth input state (joinEdge (s:=s) (t:=t) input state inherited near scale).value.1 := by
  simp [StorageGrowth, joinEdge, StoredState.recordEdge]

private theorem finishArm_metadata (valid : ℚ → Prop) {s t z u : Fin n}
    (state : StoredState.State input.graph) (path : input.graph.Path z u) (before : Metadata input valid state) :
    Metadata input valid (finishArm (s:=s) (t:=t) input state path).value.1 := by
  simpa only [Metadata, finishArm, StoredState.purchase_centers, StoredState.purchase_edges] using before

private theorem finishComplete_metadata (valid : ℚ → Prop) {s t z u : Fin n}
    (state : StoredState.State input.graph) (path : input.graph.Path s t) (before : Metadata input valid state) :
    Metadata input valid (finishComplete (z:=z) (u:=u) input state path).value.1 := by
  simpa only [Metadata, finishComplete, StoredState.purchase_centers, StoredState.purchase_edges] using before

private theorem birthArm_metadata (valid : ℚ → Prop) {s t z u : Fin n}
    (state : StoredState.State input.graph) (path : input.graph.Path z u) (scale : ℚ)
    (scale_valid : valid scale) (before : Metadata input valid state) :
    Metadata input valid (birthArm (s:=s) (t:=t) input state path scale).value.1 := by
  simp only [Metadata, birthArm, StoredState.recordBirth, StoredState.recordEdge,
    StoredState.purchase_centers, StoredState.purchase_edges, List.mem_cons]
  constructor
  · intro record member
    rcases member with rfl | member
    · exact scale_valid
    · exact before.1 record member
  · intro edge member
    rcases member with rfl | member
    · exact scale_valid
    · exact before.2 edge member

private theorem joinEdge_metadata (valid : ℚ → Prop) {s t z u v : Fin n}
    (state : StoredState.State input.graph) (inherited : input.graph.Path z u) (near : input.graph.Path z v)
    (scale : ℚ) (scale_valid : valid scale) (before : Metadata input valid state) :
    Metadata input valid (joinEdge (s:=s) (t:=t) input state inherited near scale).value.1 := by
  simp only [Metadata, joinEdge, StoredState.recordEdge, StoredState.purchase_centers,
    StoredState.purchase_edges, List.mem_cons]
  constructor
  · exact before.1
  · intro edge member
    rcases member with rfl | member
    · exact scale_valid
    · exact before.2 edge member

/-- One attachment creates at most one retained birth and one paid edge,
even if it recursively reuses many centers. -/
theorem run_storage (buying physical : Vector ℚ n) (allowance cutoff ratio threshold : ℚ) (s t : Fin n)
    (fuel : ℕ) (scale : ℚ) (z u : Fin n) (inherited : input.graph.Path z u) (state : StoredState.State input.graph) :
    StorageGrowth input state
      (run input buying physical allowance cutoff ratio threshold s t fuel scale z u inherited state).value.1 := by
  induction fuel generalizing scale z u inherited state with
  | zero => simpa only [run] using finishArm_storage (s:=s) (t:=t) input state inherited
  | succ k ih =>
      simp only [run]
      split
      · exact finishArm_storage input state inherited
      · split
        · rename_i path found
          exact finishComplete_storage input state path
        · split
          · exact birthArm_storage input state inherited scale
          · rename_i v near found
            split
            · exact joinEdge_storage input state inherited near scale
            · rename_i bypass found
              have recursive := ih (ratDiv scale ratio).value z v near state
              split <;> simpa only [joinArm] using recursive

/-- A uniform metadata invariant is preserved, provided every scale that
can be reached in this finite recursion obeys it. -/
theorem run_metadata (valid : ℚ → Prop) (buying physical : Vector ℚ n)
    (allowance cutoff ratio threshold initial : ℚ) (s t : Fin n) (R : ℕ)
    (scales : ∀ depth ≤ R, valid (scaleAt initial ratio depth)) :
    ∀ fuel depth, depth + fuel ≤ R → ∀ (z u : Fin n) (inherited : input.graph.Path z u)
      (state : StoredState.State input.graph), Metadata input valid state →
      Metadata input valid (run input buying physical allowance cutoff ratio threshold s t fuel
        (scaleAt initial ratio depth) z u inherited state).value.1 := by
  intro fuel
  induction fuel with
  | zero =>
      intro depth _ z u inherited state before
      simpa only [run] using finishArm_metadata (s:=s) (t:=t) input valid state inherited before
  | succ k ih =>
      intro depth bounded z u inherited state before
      let scale := scaleAt initial ratio depth
      have current : valid scale := scales depth (by omega)
      change Metadata input valid (run input buying physical allowance cutoff ratio threshold s t (k+1) scale z u inherited state).value.1
      simp only [run]
      split
      · exact finishArm_metadata input valid state inherited before
      · split
        · rename_i path found
          exact finishComplete_metadata input valid state path before
        · split
          · exact birthArm_metadata input valid state inherited scale current before
          · rename_i v near found
            split
            · exact joinEdge_metadata input valid state inherited near scale current before
            · rename_i bypass found
              have recursive := ih (depth + 1) (by omega) z v near state before
              have recursive' : Metadata input valid (run input buying physical allowance cutoff ratio threshold s t k
                  (ratDiv scale ratio).value z v near state).value.1 := by
                simpa only [scaleAt, ratDiv_value] using recursive
              split <;> simpa only [joinArm] using recursive'

end BuyAtBulk.Computation.Runtime.StoredAttachment
