import BuyAtBulk.Computation.Runtime.ServePathsWords

namespace BuyAtBulk.Computation.Runtime.StoredServe
open BuyAtBulk.UpperBound
open Rational
variable {n : ℕ} (input : ShortestPath.GraphEncoding n)

/-- Bought-only queries have smaller coefficient budgets than mixed queries. -/
theorem boughtRoute_words_uniform (physical : Vector ℚ n) (state : StoredState.State input.graph)
    (s t : Fin n) (threshold : ℚ) (B R : ℕ) (constant : 8 ≤ B)
    (physical_width : ∀ x : Fin n, (Code.ofRat physical[x.val]).bits ≤ B)
    (threshold_width : (Code.ofRat threshold).bits ≤ B) :
    WordsWithin (StoredAttachment.wordBudget n R B)
      (AttachmentQueries.boughtRoute input physical state s t threshold).events := by
  apply (AttachmentQueries.boughtRoute_words input physical state s t threshold B (by omega)
    physical_width threshold_width).mono
  unfold StoredAttachment.wordBudget Runtime.ShortestPath.labelBudget
  nlinarith

theorem mainPhase_words (buying physical : Vector ℚ n) (budget allowance : ℚ) (h ratio : ℕ) (threshold : ℚ)
    (s t : Fin n) (state : StoredState.State input.graph) (main : input.graph.Path s t) (scale : ℚ)
    (B : ℕ) (constant : 8 ≤ B) (ratio_ge : 2 ≤ ratio)
    (buying_width : ∀ x : Fin n, (Code.ofRat buying[x.val]).bits ≤ B)
    (physical_width : ∀ x : Fin n, (Code.ofRat physical[x.val]).bits ≤ B)
    (budget_width : (Code.ofRat budget).bits ≤ B) (allowance_width : (Code.ofRat allowance).bits ≤ B)
    (ratio_width : (Code.ofRat (ratio : ℚ)).bits ≤ B) (threshold_width : (Code.ofRat threshold).bits ≤ B)
    (scale_width : (Code.ofRat scale).bits ≤ B) (cutoff_width : (Code.ofRat (UpperBound.cutoff budget h ratio)).bits ≤ B)
    (future : ∀ depth ≤ 2 * h + 1, (Code.ofRat (StoredAttachment.scaleAt (scale / (ratio : ℚ)) (ratio : ℚ) depth)).bits ≤ B)
    (before : StoredAttachment.Metadata input (fun q => (Code.ofRat q).bits ≤ B) state) :
    WordsWithin (reuseWordBudget n h B)
      (mainPhase input buying physical budget allowance h ratio threshold s t state main scale).events := by
  let K := reuseWordBudget n h B
  let valid := fun q => (Code.ofRat q).bits ≤ B
  let first := assignCenter input buying physical allowance scale s state
  let second := assignCenter input buying physical allowance scale t first.value.state
  have base : StoredAttachment.wordBudget n 0 B ≤ K := by dsimp [K, reuseWordBudget, StoredAttachment.wordBudget]; omega
  have indices : n ≤ K := by dsimp [K, reuseWordBudget, StoredAttachment.wordBudget]; omega
  have one : 1 ≤ K := by dsimp [K, reuseWordBudget]; omega
  have scalar : B ≤ K := by dsimp [K, reuseWordBudget, StoredAttachment.wordBudget]; omega
  have first_meta : StoredAttachment.Metadata input valid first.value.state :=
    ⟨assignCenter_metadata input valid buying physical allowance scale s state scale_width before.1,
      by simpa only [first, assignCenter_edges] using before.2⟩
  have second_meta : StoredAttachment.Metadata input valid second.value.state :=
    ⟨assignCenter_metadata input valid buying physical allowance scale t first.value.state scale_width first_meta.1,
      by simpa only [second, assignCenter_edges] using first_meta.2⟩
  have first_trace := (assignCenter_words input buying physical allowance scale s state B constant
    buying_width physical_width allowance_width scale_width before.1).mono base
  have second_trace := (assignCenter_words input buying physical allowance scale t first.value.state B constant
    buying_width physical_width allowance_width scale_width first_meta.1).mono base
  have cutoff_trace := (cutoff_words budget h ratio B budget_width).mono (show 2 * B + 2 * ratio.size + 2 * h + 20 ≤ K by
    rw [SourceCoefficients.natCast_bits] at ratio_width
    dsimp [K, reuseWordBudget]; omega)
  have cheap_trace : WordsWithin K (ratLe scale (cutoff budget h ratio).value).events := by
    simpa only [ratLe, emit, cutoff_value, wordsWithin_cons, wordsWithin_nil, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true] using
      And.intro (scale_width.trans scalar) (cutoff_width.trans scalar)
  have si := ((Nat.size_le.mpr Nat.lt_two_pow_self : s.val.size ≤ s.val).trans (Nat.le_of_lt s.isLt)).trans indices
  have ti := ((Nat.size_le.mpr Nat.lt_two_pow_self : t.val.size ≤ t.val).trans (Nat.le_of_lt t.isLt)).trans indices
  have cheap_purchase : WordsWithin K (StoredState.purchase input.graph state main).events :=
    StoredState.buyWalk_words input.graph state main.val K indices one
  have purchased := purchaseMain_words input second.value.state first.value.arm main second.value.arm scale K indices one (scale_width.trans scalar)
  have middle := (boughtRoute_words_uniform input physical second.value.state first.value.center second.value.center threshold B 0 constant
    physical_width threshold_width).mono base
  simp only [first, second] at first_trace second_trace purchased middle second_meta
  simp only [mainPhase]
  split
  · simp only [emit, wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, and_true]
    aesop
  · split
    · simp only [emit, wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, forall_eq, and_true]
      aesop
    · split
      · simp only [emit, wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
          or_false, forall_eq_or_imp, forall_eq, and_true]
        aesop
      · rename_i path returned
        have reused := reuseArms_words input buying physical budget allowance h ratio threshold scale s t
          first.value.center second.value.center first.value.arm second.value.arm path second.value.state B constant ratio_ge
          buying_width physical_width budget_width allowance_width ratio_width threshold_width scale_width cutoff_width future second_meta
        simp only [first, second] at reused
        simp only [emit, wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
          or_false, forall_eq_or_imp, forall_eq, and_true]
        aesop


theorem mixedQuery_words (buying physical : Vector ℚ n) (state : StoredState.State input.graph)
    (allowance scale : ℚ) (s t : Fin n) (B R : ℕ) (constant : 8 ≤ B)
    (buying_width : ∀ x : Fin n, (Code.ofRat buying[x.val]).bits ≤ B)
    (physical_width : ∀ x : Fin n, (Code.ofRat physical[x.val]).bits ≤ B)
    (allowance_width : (Code.ofRat allowance).bits ≤ B) (scale_width : (Code.ofRat scale).bits ≤ B) :
    WordsWithin (StoredAttachment.wordBudget n R B)
        (Weights.mixed buying physical state allowance scale).events ∧
      WordsWithin (StoredAttachment.wordBudget n R B)
        (Queries.indexedPath input (Weights.mixed buying physical state allowance scale).value s t).events := by
  constructor
  · exact (Weights.mixed_words buying physical state allowance scale B (by omega)
      buying_width physical_width allowance_width scale_width).mono (by unfold StoredAttachment.wordBudget; omega)
  · apply (Queries.indexedPath_words input (Weights.mixed buying physical state allowance scale).value s t
      (22 * B + 57) (by omega) (fun v => ?_)).mono
    · unfold StoredAttachment.wordBudget; omega
    · have actual := Weights.mixedCell_bits buying physical state allowance scale v B (by omega)
        buying_width physical_width allowance_width scale_width
      simpa only [Weights.mixed, Weights.materialize_get] using Nat.add_le_add_right actual 1

def serveWordBudget (n h L : ℕ) : ℕ :=
  reuseWordBudget n h (metadataBudget h L) + gridWordBudget n (2*h+1) L + logarithmWordBudget h L + 100

/-- All scalar words, including intermediate raw normalization pairs and
all retained metadata, are bounded from the original numerical inputs. -/
theorem run_words (buying physical : Vector ℚ n) (budget allowance : ℚ) (h ratio : ℕ) (threshold : ℚ)
    (s t : Fin n) (state : StoredState.State input.graph) (L : ℕ) (constant : 8 ≤ L) (ratio_ge : 2 ≤ ratio)
    (buying_width : ∀ x : Fin n, (Code.ofRat buying[x.val]).bits ≤ L)
    (physical_width : ∀ x : Fin n, (Code.ofRat physical[x.val]).bits ≤ L)
    (budget_width : (Code.ofRat budget).bits ≤ L) (allowance_width : (Code.ofRat allowance).bits ≤ L)
    (threshold_width : (Code.ofRat threshold).bits ≤ L) (ratio_width : ratio.size ≤ L)
    (before : StoredAttachment.Metadata input (fun q => (Code.ofRat q).bits ≤ metadataBudget h L) state) :
    WordsWithin (serveWordBudget n h L)
      (run input buying physical budget allowance h ratio threshold s t state).events := by
  let B := metadataBudget h L
  let K := serveWordBudget n h L
  have LB : L ≤ B := by dsimp [B, metadataBudget, gridScalarBudget]; omega
  have BC : 8 ≤ B := by omega
  have base : StoredAttachment.wordBudget n (2*h+1) B ≤ K := by dsimp [K, serveWordBudget, B, reuseWordBudget]; omega
  have phase_base : reuseWordBudget n h B ≤ K := by dsimp [K, serveWordBudget, B]; omega
  have indices : n ≤ K := by dsimp [K, serveWordBudget, reuseWordBudget, StoredAttachment.wordBudget]; omega
  have one : 1 ≤ K := by dsimp [K, serveWordBudget]; omega
  have large : 2*h+2 ≤ K := by dsimp [K, serveWordBudget, gridWordBudget]; omega
  have si := ((Nat.size_le.mpr Nat.lt_two_pow_self : s.val.size ≤ s.val).trans (Nat.le_of_lt s.isLt)).trans indices
  have ti := ((Nat.size_le.mpr Nat.lt_two_pow_self : t.val.size ≤ t.val).trans (Nat.le_of_lt t.isLt)).trans indices
  have Dbound := Runtime.gridDepth_bound h ratio ratio_ge
  have rho : (Code.ofRat (ratio : ℚ)).bits ≤ B := by
    rw [SourceCoefficients.natCast_bits]
    dsimp [B, metadataBudget, gridScalarBudget]; omega
  have cut : (Code.ofRat (UpperBound.cutoff budget h ratio)).bits ≤ B := by
    have actual := cutoff_bits budget h ratio L budget_width
    dsimp [B, metadataBudget, gridScalarBudget]
    nlinarith
  have scalar (d : ℕ) (bounded : d ≤ 4*h+3) : (Code.ofRat (gridScale budget ratio d).value).bits ≤ B := by
    rw [gridScale_value]
    exact gridScalarBudget_scale budget ratio d (4*h+3) (L+4) (by omega) (by omega) bounded
  have scalar_trace (d : ℕ) (bounded : d ≤ 2*h+1) : WordsWithin K (gridScale budget ratio d).events := by
    apply (gridScale_words budget ratio d L budget_width).mono
    have product := Nat.mul_le_mul (Nat.add_le_add_right ratio_width 1) (Nat.add_le_add_right bounded 1)
    have BK : B ≤ K := by dsimp [K, serveWordBudget, reuseWordBudget, StoredAttachment.wordBudget]; omega
    have expression : 4*L+2*(ratio.size+1)*(d+1)+60 ≤ B := by
      dsimp [B, metadataBudget, gridScalarBudget]
      nlinarith
    omega
  have early := (boughtRoute_words_uniform input physical state s t allowance B (2*h+1) BC
    (fun x => (physical_width x).trans LB) (allowance_width.trans LB)).mono base
  have selection := (selectScale_words input buying physical state budget allowance h ratio s t L ratio_ge
    buying_width physical_width budget_width allowance_width ratio_width).mono
    (show gridWordBudget n (2*h+1) L + logarithmWordBudget h L ≤ K by dsimp [K, serveWordBudget]; omega)
  have depth := (gridDepth_words h ratio).mono (show logarithmWordBudget h ratio.size ≤ K by
    have product := Nat.mul_le_mul_right (2*h+4) (show 2*ratio.size+2*h+10 ≤ 2*L+2*h+10 by omega)
    dsimp [K, serveWordBudget, logarithmWordBudget] at *; omega)
  simp only [run]
  split
  · simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, and_true]
    aesop
  · split
    · have scale_trace := scalar_trace (gridDepth h ratio).value (by simpa only [gridDepth_value h ratio ratio_ge] using Dbound)
      have scale_width := scalar (gridDepth h ratio).value (by rw [gridDepth_value h ratio ratio_ge]; omega)
      have queries := mixedQuery_words input buying physical state allowance (gridScale budget ratio (gridDepth h ratio).value).value s t B (2*h+1) BC
        (fun x => (buying_width x).trans LB) (fun x => (physical_width x).trans LB) (allowance_width.trans LB) scale_width
      have weights := queries.1.mono base
      have route := queries.2.mono base
      split
      · simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
          or_false, forall_eq_or_imp, forall_eq, and_true]
        aesop
      · rename_i path returned
        have bought : WordsWithin K (StoredState.purchase input.graph state path).events :=
          StoredState.buyWalk_words input.graph state path.val K indices one
        simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
          or_false, forall_eq_or_imp, forall_eq, and_true]
        aesop
    · rename_i d returned
      have range := selectScale_some_range input buying physical state budget allowance h ratio s t d ratio_ge returned
      have dBound : d ≤ 2*h+1 := by omega
      have di : d.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
      have pi : (d-1).size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
      have previous_trace := scalar_trace (d-1) (by omega)
      have scale_trace := scalar_trace d dBound
      have previous_width := scalar (d-1) (by omega)
      have queries := mixedQuery_words input buying physical state allowance (gridScale budget ratio (d-1)).value s t B (2*h+1) BC
        (fun x => (buying_width x).trans LB) (fun x => (physical_width x).trans LB) (allowance_width.trans LB) previous_width
      have weights := queries.1.mono base
      have route := queries.2.mono base
      simp only [emit_value]
      split
      · simp only [emit, wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
          or_false, forall_eq_or_imp, forall_eq, and_true]
        aesop
      · rename_i main found
        have future (j : ℕ) (bound : j ≤ 2*h+1) :
            (Code.ofRat (StoredAttachment.scaleAt ((gridScale budget ratio d).value / (ratio : ℚ)) (ratio : ℚ) j)).bits ≤ B := by
          rw [gridScale_value, scaleAt_grid]
          exact gridScalarBudget_scale budget ratio (d+1+j) (4*h+3) (L+4) (by omega) (by omega) (by omega)
        have phase := (mainPhase_words input buying physical budget allowance h ratio threshold s t state main
          (gridScale budget ratio d).value B BC ratio_ge (fun x => (buying_width x).trans LB)
          (fun x => (physical_width x).trans LB) (budget_width.trans LB) (allowance_width.trans LB)
          rho (threshold_width.trans LB) (scalar d (by omega)) cut future before).mono phase_base
        simp only [emit, wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
          or_false, forall_eq_or_imp, forall_eq, and_true]
        aesop

end BuyAtBulk.Computation.Runtime.StoredServe
