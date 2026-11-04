import BuyAtBulk.Computation.Runtime.AttachmentWords
import BuyAtBulk.Computation.Serve.Assignment

namespace BuyAtBulk.Computation.Runtime.StoredServe
open BuyAtBulk.UpperBound
variable {n : ℕ} (input : ShortestPath.GraphEncoding n)

structure Assignment (z : Fin n) where
  state : StoredState.State input.graph
  born : Bool
  center : Fin n
  arm : input.graph.Path z center

def Assignment.decode {z : Fin n} (assignment : Assignment input z) : Serve.AssignmentResult input.graph z :=
  ⟨StoredState.decode input.graph assignment.state, assignment.born, assignment.center, assignment.arm⟩

def assignCenter (buying physical : Vector ℚ n) (allowance scale : ℚ) (z : Fin n)
    (state : StoredState.State input.graph) : Traced (Assignment input z) :=
  let weights := Weights.mixed buying physical state allowance scale
  let nearby := AttachmentQueries.nearRecord input weights.value scale z state.centers
  let control := weights.events ++ nearby.events ++ [⟨Operation.branch, [1]⟩]
  match nearby.value with
  | some ⟨v, arm⟩ =>
      ⟨⟨state, false, v, arm⟩, control ++ [⟨.cons, [v.val.size, 1]⟩]⟩
  | none =>
      let born := StoredState.recordBirth input.graph state z scale
      ⟨⟨born.value, true, z, .nil⟩,
        control ++ born.events ++ [⟨.cons, [z.val.size, 1]⟩, ⟨.cons, [z.val.size]⟩]⟩

theorem assignCenter_value (buying physical : Vector ℚ n) (allowance scale : ℚ) (z : Fin n)
    (state : StoredState.State input.graph) :
    Assignment.decode input (assignCenter input buying physical allowance scale z state).value =
      Serve.assignCenter input.graph (Equiv.refl _) (fun v => buying[v.val]) (fun v => physical[v.val])
        allowance scale z (StoredState.decode input.graph state) := by
  have weights : (fun v => (Weights.mixed buying physical state allowance scale).value[v.val]) =
      Attachment.mixedWeight input.graph (fun v => buying[v.val]) (fun v => physical[v.val])
        (StoredState.decode input.graph state) allowance scale := funext (Weights.mixed_get buying physical state allowance scale)
  have nearby := AttachmentQueries.nearRecord_value input (Weights.mixed buying physical state allowance scale).value scale z state.centers
  rw [weights] at nearby
  have centers : (StoredState.decode input.graph state).centers = state.centers := rfl
  simp only [assignCenter, Serve.assignCenter, centers]
  rw [← nearby]
  cases returned : (AttachmentQueries.nearRecord input (Weights.mixed buying physical state allowance scale).value scale z state.centers).value with
  | none => simp [Assignment.decode, StoredState.decode_recordBirth, returned]
  | some result => obtain ⟨v, arm⟩ := result; simp [Assignment.decode, returned]

theorem assignCenter_count (buying physical : Vector ℚ n) (allowance scale : ℚ) (z : Fin n)
    (state : StoredState.State input.graph) :
    (assignCenter input buying physical allowance scale z state).events.length ≤
      14 * n + state.centers.length * (AttachmentQueries.routeBudget n + 10) + 6 := by
  have weights := Weights.mixed_count buying physical state allowance scale
  have nearby := AttachmentQueries.nearRecord_count input (Weights.mixed buying physical state allowance scale).value scale z state.centers
  simp only [assignCenter]
  split <;> simp only [List.length_append, List.length_cons, List.length_nil, StoredState.recordBirth] <;> omega

@[simp] theorem assignCenter_bought (buying physical : Vector ℚ n) (allowance scale : ℚ) (z : Fin n)
    (state : StoredState.State input.graph) :
    (assignCenter input buying physical allowance scale z state).value.state.bought = state.bought := by
  simp only [assignCenter]
  split <;> rfl

@[simp] theorem assignCenter_edges (buying physical : Vector ℚ n) (allowance scale : ℚ) (z : Fin n)
    (state : StoredState.State input.graph) :
    (assignCenter input buying physical allowance scale z state).value.state.edges = state.edges := by
  simp only [assignCenter]
  split <;> rfl

theorem assignCenter_centers (buying physical : Vector ℚ n) (allowance scale : ℚ) (z : Fin n)
    (state : StoredState.State input.graph) :
    (assignCenter input buying physical allowance scale z state).value.state.centers.length ≤ state.centers.length + 1 := by
  simp only [assignCenter]
  split
  · exact Nat.le_succ _
  · simp [StoredState.recordBirth]

theorem assignCenter_metadata (P : ℚ → Prop) (buying physical : Vector ℚ n)
    (allowance scale : ℚ) (z : Fin n) (state : StoredState.State input.graph)
    (scale_valid : P scale) (before : ∀ record ∈ state.centers, P record.birthScale) :
    ∀ record ∈ (assignCenter input buying physical allowance scale z state).value.state.centers,
      P record.birthScale := by
  simp only [assignCenter]
  split
  · exact before
  · simp only [StoredState.recordBirth, List.mem_cons]
    intro record member
    rcases member with rfl | member
    · exact scale_valid
    · exact before record member

theorem assignCenter_words (buying physical : Vector ℚ n) (allowance scale : ℚ) (z : Fin n)
    (state : StoredState.State input.graph) (B : ℕ) (constant : 8 ≤ B)
    (buying_width : ∀ v : Fin n, (Rational.Code.ofRat buying[v.val]).bits ≤ B)
    (physical_width : ∀ v : Fin n, (Rational.Code.ofRat physical[v.val]).bits ≤ B)
    (allowance_width : (Rational.Code.ofRat allowance).bits ≤ B)
    (scale_width : (Rational.Code.ofRat scale).bits ≤ B)
    (birth_width : ∀ record ∈ state.centers, (Rational.Code.ofRat record.birthScale).bits ≤ B) :
    WordsWithin (StoredAttachment.wordBudget n 0 B)
      (assignCenter input buying physical allowance scale z state).events := by
  let K := StoredAttachment.wordBudget n 0 B
  let LW := 22 * B + 57
  have indices : n ≤ K := by dsimp [K, StoredAttachment.wordBudget]; omega
  have scalar : B ≤ K := by dsimp [K, StoredAttachment.wordBudget]; omega
  have one : 1 ≤ K := by omega
  have zi : z.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt z.isLt |>.trans indices)
  have weights := (Weights.mixed_words buying physical state allowance scale B (by omega)
    buying_width physical_width allowance_width scale_width).mono
    (show 22 * B + 56 + n ≤ K by dsimp [K, StoredAttachment.wordBudget]; omega)
  have weight_inputs (v : Fin n) :
      (Rational.Code.ofRat (Weights.mixed buying physical state allowance scale).value[v.val]).bits + 1 ≤ LW := by
    have actual := Weights.mixedCell_bits buying physical state allowance scale v B (by omega)
      buying_width physical_width allowance_width scale_width
    simp only [Weights.mixed, Weights.materialize_get]
    dsimp [LW]
    omega
  have nearby := (AttachmentQueries.nearRecord_words input (Weights.mixed buying physical state allowance scale).value
    scale z state.centers LW B (by dsimp [LW]; omega) weight_inputs scale_width birth_width).mono
    (show 2 * (LW + Runtime.ShortestPath.labelBudget n LW) + 9 + n + n + (2 * B + 22) + 1 ≤ K by
      dsimp [K, StoredAttachment.wordBudget, LW]; omega)
  simp only [assignCenter]
  split
  · rename_i v arm found
    have vi : v.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt v.isLt |>.trans indices)
    simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
    aesop
  · have born := StoredAttachment.recordBirth_words input state z scale K indices (scale_width.trans scalar)
    simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
    aesop

end BuyAtBulk.Computation.Runtime.StoredServe
