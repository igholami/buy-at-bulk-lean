import BuyAtBulk.Computation.Runtime.ServeGrid

namespace BuyAtBulk.Computation.Runtime.StoredServe
open BuyAtBulk.UpperBound
open Rational
variable {n : ℕ} (input : ShortestPath.GraphEncoding n)

theorem gridScale_bits (budget : ℚ) (ratio depth L : ℕ) (input_width : (Code.ofRat budget).bits ≤ L) :
    (Code.ofRat (UpperBound.gridScale budget ratio depth)).bits ≤ 4 * L + 2 * ratio.size * depth + 52 := by
  have literal : (Code.ofRat 2).bits = 5 := by decide
  have power := power_size ratio depth
  have denominator : (Code.ofRat ((ratio ^ depth : ℕ) : ℚ)).bits ≤ ratio.size * depth + 4 := by
    rw [SourceCoefficients.natCast_bits]
    omega
  have numerator := ratMul_result_bits 2 budget
  have divided := ratDiv_result_bits (2 * budget) ((ratio ^ depth : ℕ) : ℚ)
  rw [Nat.cast_pow] at denominator divided
  unfold UpperBound.gridScale
  nlinarith

theorem gridScale_words (budget : ℚ) (ratio depth L : ℕ) (input_width : (Code.ofRat budget).bits ≤ L) :
    WordsWithin (4 * L + 2 * (ratio.size + 1) * (depth + 1) + 60) (gridScale budget ratio depth).events := by
  let K := 4 * L + 2 * (ratio.size + 1) * (depth + 1) + 60
  have powered := (power_words ratio depth).mono (show (ratio.size + 1) * (depth + 1) + 2 ≤ K by dsimp [K]; nlinarith)
  have power := power_size ratio depth
  have integer : (ratio ^ depth).size ≤ K := by dsimp [K]; nlinarith
  have literal : (Code.ofRat 2).bits = 5 := by decide
  have denominator : (Code.ofRat ((ratio ^ depth : ℕ) : ℚ)).bits ≤ ratio.size * depth + 4 := by
    rw [SourceCoefficients.natCast_bits]
    omega
  have numerator_bits := ratMul_result_bits 2 budget
  have numerator : WordsWithin K (ratMul 2 budget).events := by
    intro event member word present
    exact (ratMul_words 2 budget event member word present).trans (by dsimp [K]; omega)
  have divided : WordsWithin K (ratDiv (2 * budget) ((ratio ^ depth : ℕ) : ℚ)).events := by
    intro event member word present
    exact (ratDiv_words _ _ event member word present).trans (by dsimp [K]; nlinarith)
  simp only [gridScale, Traced.bind_events, Traced.bind_value, power_value, ratCast, emit, emit_value,
    ratMul_value, wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_singleton, forall_eq, and_true]
  exact ⟨powered, integer, numerator, divided⟩

def gridScalarBudget (D L : ℕ) : ℕ := 4 * L + 2 * (L + 1) * (D + 1) + 64

theorem gridScalarBudget_input (D L : ℕ) : L ≤ gridScalarBudget D L := by unfold gridScalarBudget; omega

theorem gridScalarBudget_scale (budget : ℚ) (ratio depth D L : ℕ)
    (input_width : (Code.ofRat budget).bits ≤ L) (ratio_width : ratio.size ≤ L) (bounded : depth ≤ D) :
    (Code.ofRat (UpperBound.gridScale budget ratio depth)).bits ≤ gridScalarBudget D L := by
  have actual := gridScale_bits budget ratio depth L input_width
  have product := Nat.mul_le_mul ratio_width bounded
  unfold gridScalarBudget
  nlinarith

def gridWordBudget (n D L : ℕ) : ℕ :=
  let B := gridScalarBudget D L
  let LW := 22 * B + 57
  2 * (LW + Runtime.ShortestPath.labelBudget n LW) + 2 * n + B + D + 100

theorem eligibleAt_words (buying physical : Vector ℚ n) (state : StoredState.State input.graph)
    (budget allowance : ℚ) (ratio : ℕ) (s t : Fin n) (depth D L : ℕ)
    (buying_width : ∀ v : Fin n, (Code.ofRat buying[v.val]).bits ≤ L)
    (physical_width : ∀ v : Fin n, (Code.ofRat physical[v.val]).bits ≤ L)
    (budget_width : (Code.ofRat budget).bits ≤ L) (allowance_width : (Code.ofRat allowance).bits ≤ L)
    (ratio_width : ratio.size ≤ L) (bounded : depth ≤ D) :
    WordsWithin (gridWordBudget n D L) (eligibleAt input buying physical state budget allowance ratio s t depth).events := by
  let B := gridScalarBudget D L
  let LW := 22 * B + 57
  let K := gridWordBudget n D L
  have base : L ≤ B := gridScalarBudget_input D L
  have constant : 5 ≤ B := by dsimp [B, gridScalarBudget]; omega
  have scale_width : (Code.ofRat (gridScale budget ratio depth).value).bits ≤ B := by
    simpa only [gridScale_value] using gridScalarBudget_scale budget ratio depth D L budget_width ratio_width bounded
  have scale_trace := (gridScale_words budget ratio depth L budget_width).mono (show
      4 * L + 2 * (ratio.size + 1) * (depth + 1) + 60 ≤ K by
    have product := Nat.mul_le_mul (Nat.add_le_add_right ratio_width 1) (Nat.add_le_add_right bounded 1)
    dsimp [K, gridWordBudget, B, gridScalarBudget]
    nlinarith)
  have mixed := (Weights.mixed_words buying physical state allowance (gridScale budget ratio depth).value B constant
    (fun v => (buying_width v).trans base) (fun v => (physical_width v).trans base)
    (allowance_width.trans base) scale_width).mono (show 22 * B + 56 + n ≤ K by dsimp [K, gridWordBudget, B]; omega)
  have weight_inputs (v : Fin n) :
      (Code.ofRat (Weights.mixed buying physical state allowance (gridScale budget ratio depth).value).value[v.val]).bits + 1 ≤ LW := by
    have actual := Weights.mixedCell_bits buying physical state allowance (gridScale budget ratio depth).value v B constant
      (fun v => (buying_width v).trans base) (fun v => (physical_width v).trans base)
      (allowance_width.trans base) scale_width
    simp only [Weights.mixed, Weights.materialize_get]
    dsimp [LW]
    omega
  have indices : n ≤ K := by dsimp [K, gridWordBudget]; omega
  have one : 1 ≤ K := by dsimp [K, gridWordBudget]; omega
  have encoded := Queries.encodingEvents_words K indices one
  let encodedInput := ShortestPath.GraphEncoding.ofGraph input.graph (Equiv.refl _)
  let weights := (Weights.mixed buying physical state allowance (gridScale budget ratio depth).value).value
  have distances := (Runtime.ShortestPath.iterate_words encodedInput weights t n LW (by dsimp [LW]; omega) weight_inputs).mono
    (show 2 * (LW + Runtime.ShortestPath.labelBudget n LW) + 9 + n + n ≤ K by
      dsimp [K, gridWordBudget, LW, B]; omega)
  have label_width : Runtime.ShortestPath.width (Runtime.ShortestPath.iterate encodedInput weights t n).value[s.val] ≤
      Runtime.ShortestPath.labelBudget n LW := by
    rw [Runtime.ShortestPath.iterate_value]
    exact Runtime.ShortestPath.iterate_label_width encodedInput weights t n LW (by dsimp [LW]; omega) weight_inputs s
  have label : Runtime.ShortestPath.width (Runtime.ShortestPath.iterate encodedInput weights t n).value[s.val] ≤ K := by
    dsimp [K, gridWordBudget, LW, B] at *
    omega
  have si : s.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt s.isLt |>.trans indices)
  have scale_tag : Runtime.ShortestPath.width ((gridScale budget ratio depth).value : WithTop ℚ) ≤ K := by
    simp only [Runtime.ShortestPath.width]
    dsimp [K, gridWordBudget, B] at *
    omega
  simp only [eligibleAt, wordsWithin_append, Runtime.ShortestPath.read, emit, wordsWithin_cons, wordsWithin_nil,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
  exact ⟨⟨⟨⟨⟨scale_trace, mixed⟩, encoded⟩, distances⟩, si, label⟩, scale_tag, label⟩

private theorem nat_mul_bits (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact (Nat.mul_le_mul_left a (Nat.lt_size_self b).le).trans_lt
    (Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self a) (by positivity))

def logarithmWordBudget (h width : ℕ) : ℕ := (2 * width + 2 * h + 10) * (2 * h + 4) + 10

theorem gridDepth_words (h ratio : ℕ) : WordsWithin (logarithmWordBudget h ratio.size) (gridDepth h ratio).events := by
  let K := logarithmWordBudget h ratio.size
  have large : 2 * ratio.size + 2 * h + 10 ≤ K := by
    have mul := Nat.mul_le_mul_left (2 * ratio.size + 2 * h + 10) (show 1 ≤ 2 * h + 4 by omega)
    simp only [Nat.mul_one] at mul
    dsimp [K, logarithmWordBudget]
    omega
  have hs : h.size ≤ h := Nat.size_le.mpr Nat.lt_two_pow_self
  have two : (2 : ℕ).size = 2 := rfl
  have doubled : (2 * h).size ≤ 2 * h := Nat.size_le.mpr Nat.lt_two_pow_self
  have fuel : (2 * h + 1).size ≤ 2 * h + 1 := Nat.size_le.mpr Nat.lt_two_pow_self
  have twice := nat_mul_bits 2 ratio
  have product := nat_mul_bits (2 * ratio) h
  have target : (2 * ratio * h).size ≤ ratio.size + h + 2 := by omega
  have loop := (ceilingLog_words ratio (2 * ratio * h) (2 * h + 1)).mono
    (show (ratio.size + (2 * ratio * h).size + 1) * (2 * h + 1 + 2) + 2 ≤ K by
      have bound := Nat.mul_le_mul
        (show ratio.size + (2 * ratio * h).size + 1 ≤ 2 * ratio.size + 2 * h + 10 by omega)
        (show 2 * h + 1 + 2 ≤ 2 * h + 4 by omega)
      dsimp [K, logarithmWordBudget]
      omega)
  simp only [gridDepth, Traced.bind_events, Traced.bind_value, natMul, emit, wordsWithin_append,
    wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, and_true]
  repeat' apply And.intro
  all_goals first | exact loop | omega

theorem findScale_words (buying physical : Vector ℚ n) (state : StoredState.State input.graph)
    (budget allowance : ℚ) (ratio : ℕ) (s t : Fin n) (D fuel index L : ℕ)
    (buying_width : ∀ v : Fin n, (Code.ofRat buying[v.val]).bits ≤ L)
    (physical_width : ∀ v : Fin n, (Code.ofRat physical[v.val]).bits ≤ L)
    (budget_width : (Code.ofRat budget).bits ≤ L) (allowance_width : (Code.ofRat allowance).bits ≤ L)
    (ratio_width : ratio.size ≤ L) (schedule : index + fuel ≤ D + 1) :
    WordsWithin (gridWordBudget n D L)
      (findScale input buying physical state budget allowance ratio s t fuel index).events := by
  let K := gridWordBudget n D L
  have large : D + 1 ≤ K := by dsimp [K, gridWordBudget]; omega
  have one : 1 ≤ K := by omega
  induction fuel generalizing index with
  | zero =>
      have ii : index.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega : index ≤ K)
      simpa only [findScale, wordsWithin_cons, wordsWithin_nil, List.mem_singleton, forall_eq, and_true] using ii
  | succ k ih =>
      have ii : index.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega : index ≤ K)
      have ki : k.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega : k ≤ K)
      have next : (index + 1).size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega : index + 1 ≤ K)
      have eligible := eligibleAt_words input buying physical state budget allowance ratio s t index D L
        buying_width physical_width budget_width allowance_width ratio_width (by omega)
      have recursive := ih (index + 1) (by omega)
      simp only [findScale, emit_value]
      split <;> simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil, emit,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true] <;> aesop

theorem selectScale_words (buying physical : Vector ℚ n) (state : StoredState.State input.graph)
    (budget allowance : ℚ) (h ratio : ℕ) (s t : Fin n) (L : ℕ) (ratio_ge : 2 ≤ ratio)
    (buying_width : ∀ v : Fin n, (Code.ofRat buying[v.val]).bits ≤ L)
    (physical_width : ∀ v : Fin n, (Code.ofRat physical[v.val]).bits ≤ L)
    (budget_width : (Code.ofRat budget).bits ≤ L) (allowance_width : (Code.ofRat allowance).bits ≤ L)
    (ratio_width : ratio.size ≤ L) :
    WordsWithin (gridWordBudget n (2 * h + 1) L + logarithmWordBudget h L)
      (selectScale input buying physical state budget allowance h ratio s t).events := by
  let K := gridWordBudget n (2 * h + 1) L + logarithmWordBudget h L
  have Dbound := Runtime.gridDepth_bound h ratio ratio_ge
  have large : 2 * h + 2 ≤ K := by dsimp [K, gridWordBudget]; omega
  have depth := (gridDepth_words h ratio).mono (show logarithmWordBudget h ratio.size ≤ K by
    have monotone := Nat.mul_le_mul_right (2 * h + 4) (show 2 * ratio.size + 2 * h + 10 ≤ 2 * L + 2 * h + 10 by omega)
    dsimp [K, logarithmWordBudget] at *
    omega)
  have selected := (findScale_words input buying physical state budget allowance ratio s t (2 * h + 1)
    (UpperBound.gridDepth h ratio + 1) 0 L buying_width physical_width budget_width allowance_width ratio_width (by omega)).mono
    (show gridWordBudget n (2 * h + 1) L ≤ K by dsimp [K]; omega)
  have di : (UpperBound.gridDepth h ratio).size ≤ K :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega : UpperBound.gridDepth h ratio ≤ K)
  have fi : (UpperBound.gridDepth h ratio + 1).size ≤ K :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega : UpperBound.gridDepth h ratio + 1 ≤ K)
  have one : 1 ≤ K := by omega
  simp only [selectScale, gridDepth_value h ratio ratio_ge, emit, wordsWithin_append,
    wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, and_true]
  exact ⟨⟨depth, di, one, fi⟩, selected⟩

end BuyAtBulk.Computation.Runtime.StoredServe
