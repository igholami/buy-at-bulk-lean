import BuyAtBulk.Computation.Runtime.AttachmentCost

namespace BuyAtBulk.Computation.Runtime.StoredAttachment
open BuyAtBulk.UpperBound
open Rational
variable {n : ℕ} (input : ShortestPath.GraphEncoding n)

private theorem index_width (v : Fin n) : v.val.size ≤ n :=
  (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt v.isLt)

theorem finishArm_words {s t z u : Fin n} (state : StoredState.State input.graph) (path : input.graph.Path z u)
    (K : ℕ) (indices : n ≤ K) (one : 1 ≤ K) :
    WordsWithin K (finishArm (s:=s) (t:=t) input state path).events := by
  have bought := StoredState.buyWalk_words input.graph state path.val K indices one
  have zi := (index_width z).trans indices
  have ui := (index_width u).trans indices
  simp only [finishArm, StoredState.purchase, wordsWithin_append, wordsWithin_cons, wordsWithin_nil,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
  exact ⟨bought, zi, ui⟩

theorem finishComplete_words {s t z u : Fin n} (state : StoredState.State input.graph) (path : input.graph.Path s t)
    (K : ℕ) (indices : n ≤ K) (one : 1 ≤ K) :
    WordsWithin K (finishComplete (z:=z) (u:=u) input state path).events := by
  have bought := StoredState.buyWalk_words input.graph state path.val K indices one
  have si := (index_width s).trans indices
  have ti := (index_width t).trans indices
  simp only [finishComplete, StoredState.purchase, wordsWithin_append, wordsWithin_cons, wordsWithin_nil,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
  exact ⟨bought, si, ti⟩

theorem recordBirth_words (state : StoredState.State input.graph) (v : Fin n) (scale : ℚ)
    (K : ℕ) (indices : n ≤ K) (scalar : (Code.ofRat scale).bits ≤ K) :
    WordsWithin K (StoredState.recordBirth input.graph state v scale).events := by
  simp [StoredState.recordBirth, WordsWithin, (index_width v).trans indices, scalar]

theorem recordEdge_words (state : StoredState.State input.graph) {u v : Fin n} (path : input.graph.Path u v) (scale : ℚ)
    (K : ℕ) (indices : n ≤ K) (scalar : (Code.ofRat scale).bits ≤ K) :
    WordsWithin K (StoredState.recordEdge input.graph state path scale).events := by
  simp [StoredState.recordEdge, WordsWithin, (index_width u).trans indices, (index_width v).trans indices, scalar]

theorem birthArm_words {s t z u : Fin n} (state : StoredState.State input.graph) (path : input.graph.Path z u) (scale : ℚ)
    (K : ℕ) (indices : n ≤ K) (one : 1 ≤ K) (scalar : (Code.ofRat scale).bits ≤ K) :
    WordsWithin K (birthArm (s:=s) (t:=t) input state path scale).events := by
  have born := recordBirth_words input state z scale K indices scalar
  have bought := StoredState.buyWalk_words input.graph (StoredState.recordBirth input.graph state z scale).value path.val K indices one
  have edged := recordEdge_words input (StoredState.purchase input.graph (StoredState.recordBirth input.graph state z scale).value path).value path scale K indices scalar
  have zi := (index_width z).trans indices
  have ui := (index_width u).trans indices
  simp only [birthArm, wordsWithin_append, wordsWithin_cons, wordsWithin_nil,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
  exact ⟨⟨⟨born, bought⟩, edged⟩, zi, ui⟩

theorem joinEdge_words {s t z u v : Fin n} (state : StoredState.State input.graph)
    (inherited : input.graph.Path z u) (near : input.graph.Path z v) (scale : ℚ)
    (K : ℕ) (indices : n ≤ K) (one : 1 ≤ K) (scalar : (Code.ofRat scale).bits ≤ K) :
    WordsWithin K (joinEdge (s:=s) (t:=t) input state inherited near scale).events := by
  have first := StoredState.buyWalk_words input.graph state inherited.val K indices one
  have second := StoredState.buyWalk_words input.graph (StoredState.purchase input.graph state inherited).value near.val K indices one
  have reversed := Paths.reverse_words inherited.val K indices one
  have joined := Paths.append_words (Paths.reverse inherited.val).value near.val K indices one
  have erased := Paths.toPath_words (Paths.append (Paths.reverse inherited.val).value near.val).value K indices one
  have edged := recordEdge_words input (StoredState.purchase input.graph (StoredState.purchase input.graph state inherited).value near).value
    (Paths.toPath (Paths.append (Paths.reverse inherited.val).value near.val).value).value scale K indices scalar
  have zi := (index_width z).trans indices
  have ui := (index_width u).trans indices
  simp only [joinEdge, wordsWithin_append, wordsWithin_cons, wordsWithin_nil,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
  exact ⟨⟨⟨⟨⟨⟨first, second⟩, reversed⟩, joined⟩, erased⟩, edged⟩, zi, ui⟩

theorem joinArm_words {s t z u v : Fin n} (state : StoredState.State input.graph)
    (returned : input.graph.Path z v) (bypass : input.graph.Path u v)
    (K : ℕ) (indices : n ≤ K) (one : 1 ≤ K) :
    WordsWithin K (joinArm (s:=s) (t:=t) input state returned bypass).events := by
  have reversed := Paths.reverse_words bypass.val K indices one
  have joined := Paths.append_words returned.val (Paths.reverse bypass.val).value K indices one
  have erased := Paths.toPath_words (Paths.append returned.val (Paths.reverse bypass.val).value).value K indices one
  have zi := (index_width z).trans indices
  have ui := (index_width u).trans indices
  simp only [joinArm, wordsWithin_append, wordsWithin_cons, wordsWithin_nil,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
  exact ⟨⟨⟨reversed, joined⟩, erased⟩, zi, ui⟩

def scaleAt (initial ratio : ℚ) : ℕ → ℚ
  | 0 => initial
  | depth + 1 => scaleAt initial ratio depth / ratio

def scaleExpression (initial ratio : ℚ) : ℕ → Expr
  | 0 => .literal (Code.ofRat initial)
  | depth + 1 => .mul (scaleExpression initial ratio depth) (.inv (.literal (Code.ofRat ratio)))

@[simp] theorem scaleExpression_value (initial ratio : ℚ) (depth : ℕ) :
    (scaleExpression initial ratio depth).value = scaleAt initial ratio depth := by
  induction depth with
  | zero => simp [scaleExpression, scaleAt, Expr.value]
  | succ k ih => simp [scaleExpression, scaleAt, Expr.value, ih, div_eq_mul_inv]

@[simp] theorem scaleExpression_size (initial ratio : ℚ) (depth : ℕ) :
    (scaleExpression initial ratio depth).treeSize = 3 * depth + 1 := by
  induction depth with
  | zero => rfl
  | succ k ih => simp [scaleExpression, Expr.treeSize, ih]; omega

theorem scaleExpression_leaves (initial ratio : ℚ) (depth L : ℕ)
    (initial_width : (Code.ofRat initial).bits + 1 ≤ L) (ratio_width : (Code.ofRat ratio).bits + 1 ≤ L) :
    (scaleExpression initial ratio depth).maxLeafBudget ≤ L := by
  induction depth with
  | zero => exact initial_width
  | succ k ih => simpa only [scaleExpression, Expr.maxLeafBudget] using max_le ih ratio_width

def scalarBudget (depth L : ℕ) : ℕ := 2 * (3 * depth + 1) * L + 2

theorem scaleAt_bits (initial ratio : ℚ) (depth L : ℕ) (positive : 0 < L)
    (initial_width : (Code.ofRat initial).bits + 1 ≤ L) (ratio_width : (Code.ofRat ratio).bits + 1 ≤ L) :
    (Code.ofRat (scaleAt initial ratio depth)).bits ≤ scalarBudget depth L := by
  simpa only [scaleExpression_value, scaleExpression_size, scalarBudget] using
    (scaleExpression initial ratio depth).normalized_bits L positive
      (scaleExpression_leaves initial ratio depth L initial_width ratio_width)

def wordBudget (n R B : ℕ) : ℕ :=
  2 * ((22 * B + 57) + Runtime.ShortestPath.labelBudget n (22 * B + 57)) +
    4 * B + 2 * n + R + 100

/-- The scale schedule is an explicit hypothesis here; `scaleAt_bits`
discharges it with an input-derived polynomial budget below. -/
theorem run_words_of_scalars (buying physical : Vector ℚ n)
    (allowance cutoff ratio threshold initial : ℚ) (s t : Fin n) (R B : ℕ)
    (constant : 8 ≤ B)
    (buying_width : ∀ v : Fin n, (Code.ofRat buying[v.val]).bits ≤ B)
    (physical_width : ∀ v : Fin n, (Code.ofRat physical[v.val]).bits ≤ B)
    (allowance_width : (Code.ofRat allowance).bits ≤ B)
    (cutoff_width : (Code.ofRat cutoff).bits ≤ B)
    (ratio_width : (Code.ofRat ratio).bits ≤ B)
    (threshold_width : (Code.ofRat threshold).bits ≤ B)
    (scales : ∀ depth ≤ R, (Code.ofRat (scaleAt initial ratio depth)).bits ≤ B) :
    ∀ fuel depth, depth + fuel ≤ R → ∀ (z u : Fin n) (inherited : input.graph.Path z u)
      (state : StoredState.State input.graph),
      (∀ record ∈ state.centers, (Code.ofRat record.birthScale).bits ≤ B) →
      WordsWithin (wordBudget n R B)
        (run input buying physical allowance cutoff ratio threshold s t fuel
          (scaleAt initial ratio depth) z u inherited state).events := by
  let K := wordBudget n R B
  let LW := 22 * B + 57
  have indices : n ≤ K := by dsimp [K, wordBudget]; omega
  have one : 1 ≤ K := by dsimp [K, wordBudget]; omega
  have scalar : B ≤ K := by dsimp [K, wordBudget]; omega
  have index_width (v : Fin n) : v.val.size ≤ K :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_of_lt v.isLt |>.trans indices)
  have main_budget : 2 * (LW + Runtime.ShortestPath.labelBudget n LW) + 9 + n + n + (2 * B + 24) + 1 ≤ K := by
    dsimp [K, wordBudget, LW]
    omega
  have near_budget : 2 * (LW + Runtime.ShortestPath.labelBudget n LW) + 9 + n + n + (2 * B + 22) + 1 ≤ K := by
    omega
  have bought_budget : 2 * ((10 * B + 25) + Runtime.ShortestPath.labelBudget n (10 * B + 25)) + 9 + n + n + B + 1 ≤ K := by
    have monotone : Runtime.ShortestPath.labelBudget n (10 * B + 25) ≤ Runtime.ShortestPath.labelBudget n LW := by
      unfold Runtime.ShortestPath.labelBudget
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (show 10 * B + 25 ≤ LW by dsimp [LW]; omega)) 3
    dsimp [K, wordBudget, LW] at *
    omega
  intro fuel
  induction fuel with
  | zero =>
      intro depth _ z u inherited state _
      have terminal := finishArm_words (s:=s) (t:=t) input state inherited K indices one
      simpa only [run, wordsWithin_cons, List.mem_singleton, forall_eq] using
        And.intro (show 0 ≤ K by omega) terminal
  | succ k ih =>
      intro depth bounded z u inherited state birth_width
      let scale := scaleAt initial ratio depth
      have scale_width : (Code.ofRat scale).bits ≤ B := scales depth (by omega)
      have scale_in_K := scale_width.trans scalar
      have cutoff_in_K := cutoff_width.trans scalar
      have control : WordsWithin K (ratLe scale cutoff).events := by
        simpa [ratLe, emit, WordsWithin] using And.intro scale_in_K cutoff_in_K
      have fi : (k + 1).size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans
        (show k + 1 ≤ K by dsimp [K, wordBudget]; omega)
      have weights := (Weights.mixed_words buying physical state allowance scale B (by omega)
        buying_width physical_width allowance_width scale_width).mono
        (show 22 * B + 56 + n ≤ K by dsimp [K, wordBudget]; omega)
      have weight_inputs (v : Fin n) :
          (Code.ofRat (Weights.mixed buying physical state allowance scale).value[v.val]).bits + 1 ≤ LW := by
        have actual := Weights.mixedCell_bits buying physical state allowance scale v B (by omega)
          buying_width physical_width allowance_width scale_width
        simp only [Weights.mixed, Weights.materialize_get]
        dsimp [LW]
        omega
      have literal : (Code.ofRat 16).bits = 8 := by decide
      have limit_width : (Code.ofRat (scale / 16)).bits ≤ 2 * B + 24 := by
        have actual := ratDiv_result_bits scale 16
        omega
      have limit : WordsWithin K (ratDiv scale 16).events := by
        intro event member word present
        exact (ratDiv_words scale 16 event member word present).trans (by omega)
      have queried := (Queries.shortRoute_words input (Weights.mixed buying physical state allowance scale).value
        s t (scale / 16) LW (2 * B + 24) (by dsimp [LW]; omega) weight_inputs limit_width).mono main_budget
      have nearby := (AttachmentQueries.nearRecord_words input (Weights.mixed buying physical state allowance scale).value
        scale z state.centers LW B (by dsimp [LW]; omega) weight_inputs scale_width birth_width).mono near_budget
      have reduced : WordsWithin K (ratDiv scale ratio).events := by
        intro event member word present
        exact (ratDiv_words scale ratio event member word present).trans (by dsimp [K, wordBudget]; omega)
      change WordsWithin K (run input buying physical allowance cutoff ratio threshold s t (k + 1) scale z u inherited state).events
      simp only [run]
      split
      · have terminal := finishArm_words (s:=s) (t:=t) input state inherited K indices one
        simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil, List.mem_singleton, forall_eq]
        aesop
      · split
        · rename_i path found
          have terminal := finishComplete_words (z:=z) (u:=u) input state path K indices one
          simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil, ratDiv_value, List.mem_singleton, forall_eq]
          aesop
        · split
          · have terminal := birthArm_words (s:=s) (t:=t) input state inherited scale K indices one scale_in_K
            simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil, ratDiv_value, List.mem_singleton, forall_eq]
            aesop
          · rename_i v nearPath found
            have bought := (AttachmentQueries.boughtRoute_words input physical state u v threshold B (by omega)
              physical_width threshold_width).mono bought_budget
            split
            · have terminal := joinEdge_words (s:=s) (t:=t) input state inherited nearPath scale K indices one scale_in_K
              simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil, ratDiv_value, List.mem_singleton, forall_eq]
              aesop
            · rename_i bypass found
              have recursive := ih (depth + 1) (by omega) z v nearPath state birth_width
              have recursive' : WordsWithin K (run input buying physical allowance cutoff ratio threshold s t k
                  (scale / ratio) z v nearPath state).events := by
                simpa only [scaleAt] using recursive
              split
              · rename_i returned found
                have terminal := joinArm_words (s:=s) (t:=t) input
                  (run input buying physical allowance cutoff ratio threshold s t k (ratDiv scale ratio).value z v nearPath state).value.1
                  returned bypass K indices one
                simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil, ratDiv_value, List.mem_singleton, forall_eq]
                simp only [ratDiv_value] at terminal
                aesop
              · have si := index_width s
                have ti := index_width t
                simp only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil, ratDiv_value,
                  List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
                aesop

/-- Fully input-derived width bound. All initial scalar and vector widths
are bounded by L; every later recursive scale is certified by its explicit
linear-size expression tree. -/
theorem run_words (buying physical : Vector ℚ n)
    (allowance cutoff ratio threshold initial : ℚ) (s t : Fin n) (fuel L : ℕ)
    (constant : 8 ≤ L)
    (buying_width : ∀ v : Fin n, (Code.ofRat buying[v.val]).bits ≤ L)
    (physical_width : ∀ v : Fin n, (Code.ofRat physical[v.val]).bits ≤ L)
    (allowance_width : (Code.ofRat allowance).bits ≤ L)
    (cutoff_width : (Code.ofRat cutoff).bits ≤ L)
    (ratio_width : (Code.ofRat ratio).bits + 1 ≤ L)
    (threshold_width : (Code.ofRat threshold).bits ≤ L)
    (initial_width : (Code.ofRat initial).bits + 1 ≤ L)
    (z u : Fin n) (inherited : input.graph.Path z u) (state : StoredState.State input.graph)
    (birth_width : ∀ record ∈ state.centers, (Code.ofRat record.birthScale).bits ≤ L) :
    WordsWithin (wordBudget n fuel (scalarBudget fuel L))
      (run input buying physical allowance cutoff ratio threshold s t fuel initial z u inherited state).events := by
  have base : L ≤ scalarBudget fuel L := by
    unfold scalarBudget
    have bound := Nat.mul_le_mul_right L (show 1 ≤ 2 * (3 * fuel + 1) by omega)
    simp only [Nat.one_mul] at bound
    omega
  have schedule (depth : ℕ) (bounded : depth ≤ fuel) :
      (Code.ofRat (scaleAt initial ratio depth)).bits ≤ scalarBudget fuel L := by
    have actual := scaleAt_bits initial ratio depth L (by omega) initial_width ratio_width
    have monotone : scalarBudget depth L ≤ scalarBudget fuel L := by
      unfold scalarBudget
      exact Nat.add_le_add_right (Nat.mul_le_mul_right L (by omega)) 2
    exact actual.trans monotone
  have result := run_words_of_scalars input buying physical allowance cutoff ratio threshold initial s t
    fuel (scalarBudget fuel L) (constant.trans base)
    (fun v => (buying_width v).trans base) (fun v => (physical_width v).trans base)
    (allowance_width.trans base) (cutoff_width.trans base)
    (((Nat.le_add_right _ 1).trans ratio_width).trans base) (threshold_width.trans base) schedule
    fuel 0 (by omega) z u inherited state (fun record member => (birth_width record member).trans base)
  simpa only [scaleAt] using result

/-- Full ConnectEndpoint refinement, primitive schedule and normalized/raw
rational-word budget in the declared rational word-operation model. -/
theorem run_runtime (buying physical : Vector ℚ n)
    (allowance cutoff ratio threshold initial : ℚ) (s t : Fin n) (fuel L : ℕ)
    (constant : 8 ≤ L)
    (buying_width : ∀ v : Fin n, (Code.ofRat buying[v.val]).bits ≤ L)
    (physical_width : ∀ v : Fin n, (Code.ofRat physical[v.val]).bits ≤ L)
    (allowance_width : (Code.ofRat allowance).bits ≤ L)
    (cutoff_width : (Code.ofRat cutoff).bits ≤ L)
    (ratio_width : (Code.ofRat ratio).bits + 1 ≤ L)
    (threshold_width : (Code.ofRat threshold).bits ≤ L)
    (initial_width : (Code.ofRat initial).bits + 1 ≤ L)
    (z u : Fin n) (inherited : input.graph.Path z u) (state : StoredState.State input.graph)
    (birth_width : ∀ record ∈ state.centers, (Code.ofRat record.birthScale).bits ≤ L) :
    decodeResult input (run input buying physical allowance cutoff ratio threshold s t fuel initial z u inherited state).value =
      Attachment.run input.graph (Equiv.refl _) (fun v => buying[v.val]) (fun v => physical[v.val])
        allowance cutoff ratio threshold s t fuel initial z u inherited (StoredState.decode input.graph state) ∧
    (run input buying physical allowance cutoff ratio threshold s t fuel initial z u inherited state).events.length ≤
      (fuel + 1) * stepBudget n state.centers.length ∧
    WordsWithin (wordBudget n fuel (scalarBudget fuel L))
      (run input buying physical allowance cutoff ratio threshold s t fuel initial z u inherited state).events :=
  ⟨run_value input buying physical allowance cutoff ratio threshold s t fuel initial z u inherited state,
    run_count input buying physical allowance cutoff ratio threshold s t fuel initial z u inherited state,
    run_words input buying physical allowance cutoff ratio threshold initial s t fuel L constant buying_width
      physical_width allowance_width cutoff_width ratio_width threshold_width initial_width z u inherited state birth_width⟩

end BuyAtBulk.Computation.Runtime.StoredAttachment
