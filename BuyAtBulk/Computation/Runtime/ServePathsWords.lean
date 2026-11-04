import BuyAtBulk.Computation.Runtime.ServeMetadata

namespace BuyAtBulk.Computation.Runtime.StoredServe
open BuyAtBulk.UpperBound
open Rational
variable {n : ℕ} (input : ShortestPath.GraphEncoding n)

private theorem nat_mul_bits (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact (Nat.mul_le_mul_left a (Nat.lt_size_self b).le).trans_lt
    (Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self a) (by positivity))

theorem cutoff_bits (budget : ℚ) (h ratio L : ℕ) (input_width : (Code.ofRat budget).bits ≤ L) :
    (Code.ofRat (UpperBound.cutoff budget h ratio)).bits ≤ 2 * L + 2 * ratio.size + 2 * h + 14 := by
  have hs : h.size ≤ h := Nat.size_le.mpr Nat.lt_two_pow_self
  have product := nat_mul_bits ratio h
  have denominator : (Code.ofRat ((ratio * h : ℕ) : ℚ)).bits ≤ ratio.size + h + 3 := by
    rw [SourceCoefficients.natCast_bits]
    omega
  have divided := ratDiv_result_bits budget ((ratio * h : ℕ) : ℚ)
  rw [Nat.cast_mul] at divided denominator
  unfold UpperBound.cutoff
  omega

theorem cutoff_words (budget : ℚ) (h ratio L : ℕ) (input_width : (Code.ofRat budget).bits ≤ L) :
    WordsWithin (2 * L + 2 * ratio.size + 2 * h + 20) (cutoff budget h ratio).events := by
  let K := 2 * L + 2 * ratio.size + 2 * h + 20
  have hs : h.size ≤ h := Nat.size_le.mpr Nat.lt_two_pow_self
  have product := nat_mul_bits ratio h
  have denominator : (Code.ofRat ((ratio * h : ℕ) : ℚ)).bits ≤ ratio.size + h + 3 := by
    rw [SourceCoefficients.natCast_bits]
    omega
  have quotient : WordsWithin K (ratDiv budget ((ratio * h : ℕ) : ℚ)).events := by
    intro event member word present
    exact (ratDiv_words _ _ event member word present).trans (by dsimp [K]; omega)
  have ri : ratio.size ≤ K := by dsimp [K]; omega
  have hi : h.size ≤ K := by dsimp [K]; omega
  have pi : (ratio * h).size ≤ K := by dsimp [K]; omega
  simp only [cutoff, Traced.bind_events, Traced.bind_value, natMul, ratCast, emit, wordsWithin_append,
    wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, and_true]
  exact ⟨⟨ri, hi⟩, pi, quotient⟩

private theorem index_width (v : Fin n) : v.val.size ≤ n :=
  (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt v.isLt)

theorem joinRoutes_words {s t u v : Fin n} (sarm : input.graph.Path s u)
    (middle : input.graph.Path u v) (tarm : input.graph.Path t v) (K : ℕ) (indices : n ≤ K) (one : 1 ≤ K) :
    WordsWithin K (joinRoutes input sarm middle tarm).events := by
  have reversed := Paths.reverse_words tarm.val K indices one
  have left := Paths.append_words sarm.val middle.val K indices one
  have right := Paths.append_words (Paths.append sarm.val middle.val).value (Paths.reverse tarm.val).value K indices one
  have simple := Paths.toPath_words (Paths.append (Paths.append sarm.val middle.val).value (Paths.reverse tarm.val).value).value K indices one
  simpa only [joinRoutes, wordsWithin_append] using And.intro (And.intro (And.intro reversed left) right) simple

theorem purchaseMain_words {s t u v : Fin n} (state : StoredState.State input.graph)
    (sarm : input.graph.Path s u) (main : input.graph.Path s t) (tarm : input.graph.Path t v) (scale : ℚ)
    (K : ℕ) (indices : n ≤ K) (one : 1 ≤ K) (scalar : (Code.ofRat scale).bits ≤ K) :
    WordsWithin K (purchaseMain input state sarm main tarm scale).events := by
  have first := StoredState.buyWalk_words input.graph state sarm.val K indices one
  have second := StoredState.buyWalk_words input.graph (StoredState.purchase input.graph state sarm).value main.val K indices one
  have third := StoredState.buyWalk_words input.graph
    (StoredState.purchase input.graph (StoredState.purchase input.graph state sarm).value main).value tarm.val K indices one
  have reversed := Paths.reverse_words sarm.val K indices one
  have left := Paths.append_words (Paths.reverse sarm.val).value main.val K indices one
  have right := Paths.append_words (Paths.append (Paths.reverse sarm.val).value main.val).value tarm.val K indices one
  have simple := Paths.toPath_words (Paths.append (Paths.append (Paths.reverse sarm.val).value main.val).value tarm.val).value K indices one
  have edged := StoredAttachment.recordEdge_words input
    (StoredState.purchase input.graph (StoredState.purchase input.graph (StoredState.purchase input.graph state sarm).value main).value tarm).value
    (Paths.toPath (Paths.append (Paths.append (Paths.reverse sarm.val).value main.val).value tarm.val).value).value scale K indices scalar
  simpa only [purchaseMain, StoredState.purchase, wordsWithin_append] using
    And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro first second) third) reversed) left) right) simple) edged

def reuseWordBudget (n h B : ℕ) : ℕ :=
  StoredAttachment.wordBudget n (2 * h + 1) B + logarithmWordBudget h B + (4 * B + 2 * h + 20) + 10

theorem reuseArms_words (buying physical : Vector ℚ n) (budget allowance : ℚ) (h ratio : ℕ) (threshold scale : ℚ)
    (s t u v : Fin n) (sarm : input.graph.Path s u) (tarm : input.graph.Path t v)
    (middle : input.graph.Path u v) (state : StoredState.State input.graph) (B : ℕ) (constant : 8 ≤ B) (ratio_ge : 2 ≤ ratio)
    (buying_width : ∀ x : Fin n, (Code.ofRat buying[x.val]).bits ≤ B)
    (physical_width : ∀ x : Fin n, (Code.ofRat physical[x.val]).bits ≤ B)
    (budget_width : (Code.ofRat budget).bits ≤ B) (allowance_width : (Code.ofRat allowance).bits ≤ B)
    (ratio_width : (Code.ofRat (ratio : ℚ)).bits ≤ B) (threshold_width : (Code.ofRat threshold).bits ≤ B)
    (scale_width : (Code.ofRat scale).bits ≤ B) (cutoff_width : (Code.ofRat (UpperBound.cutoff budget h ratio)).bits ≤ B)
    (future : ∀ depth ≤ 2 * h + 1, (Code.ofRat (StoredAttachment.scaleAt (scale / (ratio : ℚ)) (ratio : ℚ) depth)).bits ≤ B)
    (before : StoredAttachment.Metadata input (fun q => (Code.ofRat q).bits ≤ B) state) :
    WordsWithin (reuseWordBudget n h B)
      (reuseArms input buying physical budget allowance h ratio threshold scale s t u v sarm tarm middle state).events := by
  let K := reuseWordBudget n h B
  let D := (gridDepth h ratio).value
  let cut := (cutoff budget h ratio).value
  let base := (ratCast ratio).value
  let lowered := (ratDiv scale base).value
  let valid := fun q => (Code.ofRat q).bits ≤ B
  have Dbound : D ≤ 2 * h + 1 := by simpa only [D, gridDepth_value h ratio ratio_ge] using Runtime.gridDepth_bound h ratio ratio_ge
  have base_width : (Code.ofRat base).bits ≤ B := ratio_width
  have cut_width : (Code.ofRat cut).bits ≤ B := by simpa only [cut, cutoff_value] using cutoff_width
  have schedule (depth : ℕ) (bounded : depth ≤ 2 * h + 1) : valid (StoredAttachment.scaleAt lowered base depth) := by
    simpa only [valid, lowered, base, ratDiv_value, ratCast, emit_value] using future depth bounded
  let first := StoredAttachment.run input buying physical allowance cut base threshold s t D lowered s u sarm state
  have first_meta : StoredAttachment.Metadata input valid first.value.1 := by
    simpa only [first, StoredAttachment.scaleAt] using StoredAttachment.run_metadata input valid buying physical allowance cut base threshold
      lowered s t (2 * h + 1) schedule D 0 (by omega) s u sarm state before
  have first_words : WordsWithin (StoredAttachment.wordBudget n (2 * h + 1) B) first.events := by
    simpa only [first, StoredAttachment.scaleAt] using StoredAttachment.run_words_of_scalars input buying physical allowance cut base threshold
      lowered s t (2 * h + 1) B constant buying_width physical_width allowance_width cut_width base_width threshold_width schedule
      D 0 (by omega) s u sarm state before.1
  have second_words := StoredAttachment.run_words_of_scalars input buying physical allowance cut base threshold
    lowered s t (2 * h + 1) B constant buying_width physical_width allowance_width cut_width base_width threshold_width schedule
    D 0 (by omega) t v tarm first.value.1 first_meta.1
  simp only [StoredAttachment.scaleAt] at second_words
  have cutoff_trace := (cutoff_words budget h ratio B budget_width).mono (show 2 * B + 2 * ratio.size + 2 * h + 20 ≤ K by
    rw [SourceCoefficients.natCast_bits] at ratio_width
    dsimp [K, reuseWordBudget]
    omega)
  have depth_trace := (gridDepth_words h ratio).mono (show logarithmWordBudget h ratio.size ≤ K by
    rw [SourceCoefficients.natCast_bits] at ratio_width
    have increasing := Nat.mul_le_mul_right (2 * h + 4) (show 2 * ratio.size + 2 * h + 10 ≤ 2 * B + 2 * h + 10 by omega)
    dsimp [K, reuseWordBudget, logarithmWordBudget] at *
    omega)
  have cast_trace : WordsWithin K (ratCast ratio).events := by
    rw [SourceCoefficients.natCast_bits] at ratio_width
    simp only [ratCast, emit, wordsWithin_cons, wordsWithin_nil, List.mem_singleton, forall_eq, and_true]
    dsimp [K, reuseWordBudget]
    omega
  have lowered_trace : WordsWithin K (ratDiv scale base).events := by
    intro event member word present
    exact (ratDiv_words scale base event member word present).trans (by dsimp [K, reuseWordBudget, StoredAttachment.wordBudget]; omega)
  have first_trace := first_words.mono (show StoredAttachment.wordBudget n (2 * h + 1) B ≤ K by dsimp [K, reuseWordBudget]; omega)
  have second_trace := second_words.mono (show StoredAttachment.wordBudget n (2 * h + 1) B ≤ K by dsimp [K, reuseWordBudget]; omega)
  have indices : n ≤ K := by dsimp [K, reuseWordBudget, StoredAttachment.wordBudget]; omega
  have one : 1 ≤ K := by dsimp [K, reuseWordBudget]; omega
  have si := (index_width s).trans indices
  have ti := (index_width t).trans indices
  simp only [D, cut, base, lowered, first] at first_trace second_trace lowered_trace
  simp only [reuseArms]
  split
  · simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, and_true]
    aesop
  · rename_i returnedS found
    split
    · simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, forall_eq, and_true]
      aesop
    · rename_i returnedT found
      have joined := joinRoutes_words input returnedS middle returnedT K indices one
      simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, forall_eq, and_true]
      aesop

end BuyAtBulk.Computation.Runtime.StoredServe
