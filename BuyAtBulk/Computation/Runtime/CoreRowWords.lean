import BuyAtBulk.Computation.Runtime.CoreDatabase

namespace BuyAtBulk.Computation.Runtime.StoredCore
open BuyAtBulk.UpperBound
open Rational
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

theorem emptyState_words (K : ℕ) (indices : n ≤ K) (one : 1 ≤ K) :
    WordsWithin K (emptyState input).events := by
  have flags := Weights.materialize_words (fun _ : Fin n => emit .write [1] false) (fun _ => 1) K indices
    (by intro; simpa [emit] using one) (by intro; exact one)
  simpa only [emptyState, wordsWithin_append, wordsWithin_cons, wordsWithin_nil,
    List.mem_singleton, forall_eq, and_true] using And.intro flags one

theorem rowFromDistances_words (buying : Vector ℚ n) (radius : ℚ) (mate : Fin n)
    (distances : Vector (WithTop ℚ) n) (B : ℕ) (constant : 3 ≤ B)
    (buy_width : ∀ v : Fin n, (Code.ofRat buying[v.val]).bits ≤ B)
    (radius_width : (Code.ofRat radius).bits ≤ B)
    (labels_width : ∀ v : Fin n, Runtime.ShortestPath.width distances[v.val] ≤ B) :
    WordsWithin (12*B+40+n) (rowFromDistances buying radius mate distances).events := by
  let K := 12*B+40+n
  have ni : n ≤ K := by dsimp [K]; omega
  have one : 1 ≤ K := by dsimp [K]; omega
  have mi := ((Nat.size_le.mpr Nat.lt_two_pow_self : mate.val.size ≤ mate.val).trans (Nat.le_of_lt mate.isLt)).trans ni
  have radius_b : (Code.ofRat radius).bits ≤ K := radius_width.trans (by dsimp[K];omega)
  have distance_bits : (Code.ofRat ((distances[mate.val]).untopD 0)).bits ≤ B := by
    have actual := labels_width mate
    cases label : distances[mate.val] with
    | top => simp [label, Code.ofRat, Code.bits]; omega
    | coe q =>
        simp only [label, Runtime.ShortestPath.width] at actual
        simpa only [label, WithTop.untopD_coe] using (by omega : (Code.ofRat q).bits ≤ B)
  have cell_trace (v : Fin n) : WordsWithin K ((do
      let buy ← readRat buying v
      let label ← Runtime.ShortestPath.read distances v
      tollFromLabel buy radius label) : Traced ℚ).events := by
    have vi := ((Nat.size_le.mpr Nat.lt_two_pow_self : v.val.size ≤ v.val).trans (Nat.le_of_lt v.isLt)).trans ni
    have toll := (tollFromLabel_words buying[v.val] radius distances[v.val] B (buy_width v) radius_width (labels_width v)).mono
      (show 12*B+40 ≤ K by dsimp[K];omega)
    simp only [Traced.bind_events, Traced.bind_value, readRat, Runtime.ShortestPath.read, emit_value,
      wordsWithin_append, emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, and_true]
    exact ⟨⟨vi, (buy_width v).trans (by dsimp[K];omega)⟩, ⟨vi, (labels_width v).trans (by dsimp[K];omega)⟩, toll⟩
  have cell_bits (v : Fin n) : (Code.ofRat ((do
      let buy ← readRat buying v
      let label ← Runtime.ShortestPath.read distances v
      tollFromLabel buy radius label) : Traced ℚ).value).bits ≤ K := by
    have actual := tollFromLabel_bits buying[v.val] radius distances[v.val] B (buy_width v) radius_width (labels_width v)
    simp only [Traced.bind_value, readRat, Runtime.ShortestPath.read, emit_value]
    exact actual.trans (by dsimp[K];omega)
  have cells := Weights.materialize_words _ (fun q : ℚ => (Code.ofRat q).bits) K ni cell_trace cell_bits
  have nn := (Nat.size_le.mpr Nat.lt_two_pow_self : n.size ≤ n).trans ni
  have label_b := (labels_width mate).trans (show B ≤ K by dsimp[K];omega)
  have distance_b := distance_bits.trans (show B ≤ K by dsimp[K];omega)
  simp only [rowFromDistances, Traced.bind_events, Traced.bind_value, Runtime.ShortestPath.read, emit_value,
    ratLess, wordsWithin_append, emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, and_true]
  aesop

def rowScalarBudget (h L : ℕ) := 2*StoredServe.gridScalarBudget (2*h+1) L+40

def rowLabelBudget (n h L : ℕ) := Runtime.ShortestPath.labelBudget n (22*rowScalarBudget h L+57)

def rowWordBudget (n h L : ℕ) :=
  StoredAttachment.wordBudget n (2*h+1) (rowScalarBudget h L)+
    16*(n+1)*(rowScalarBudget h L+rowLabelBudget n h L+10)+n+h+2*h+100

def rowTollBudget (n h L : ℕ) := 10*(rowScalarBudget h L+rowLabelBudget n h L)+24


theorem materializeRow_runtime (buying physical : Vector ℚ n) (budget : ℚ) (allowance : Vector ℚ h)
    (source target : Vector (Fin n) h) (ratio : ℕ) (ratio_ge : 2 ≤ ratio) (raw : Core.RawRow h ratio)
    (L : ℕ) (constant : 8 ≤ L)
    (buying_width : ∀ v : Fin n, (Code.ofRat buying[v.val]).bits ≤ L)
    (physical_width : ∀ v : Fin n, (Code.ofRat physical[v.val]).bits ≤ L)
    (budget_width : (Code.ofRat budget).bits ≤ L) (allowance_width : ∀ i : Fin h, (Code.ofRat allowance[i.val]).bits ≤ L)
    (ratio_width : ratio.size ≤ L) :
    WordsWithin (rowWordBudget n h L) (materializeRow input buying physical budget allowance source target ratio raw).events ∧
      (Code.ofRat (materializeRow input buying physical budget allowance source target ratio raw).value.radius).bits ≤ rowScalarBudget h L ∧
      ∀ v : Fin n, (Code.ofRat (materializeRow input buying physical budget allowance source target ratio raw).value.toll[v.val]).bits ≤ rowTollBudget n h L := by
  let A := rowScalarBudget h L
  let W := 22*A+57
  let R := rowLabelBudget n h L
  let B := A+R
  let K := rowWordBudget n h L
  let scale := StoredServe.gridScale budget ratio raw.2.2
  let weights := Weights.mixed buying physical (emptyState input).value allowance[raw.1.val] scale.value
  let encoded := ShortestPath.GraphEncoding.ofGraph input.graph (Equiv.refl _)
  let origin := Core.rowSource (fun i => source[i.val]) (fun i => target[i.val]) raw.2.1 raw.1
  let mate := Core.rowMate (fun i => source[i.val]) (fun i => target[i.val]) raw.2.1 raw.1
  let distances := Runtime.ShortestPath.iterate encoded weights.value origin n
  let radius := ratDiv scale.value 16
  have raw_bound : raw.2.2.val ≤ 2*h+1 := by
    have actual := raw.2.2.isLt
    have depth := Runtime.gridDepth_bound h ratio ratio_ge
    omega
  have LA : L ≤ A := by dsimp[A,rowScalarBudget,StoredServe.gridScalarBudget]; omega
  have AC : 8 ≤ A := by omega
  have base : StoredAttachment.wordBudget n (2*h+1) A ≤ K := by dsimp[K,rowWordBudget,A];omega
  have ni : n ≤ K := by dsimp[K,rowWordBudget];omega
  have hi : h ≤ K := by dsimp[K,rowWordBudget];omega
  have one : 1 ≤ K := by dsimp[K,rowWordBudget];omega
  have hk : 2*h+1 ≤ K := by dsimp[K,rowWordBudget];omega
  have AK : A ≤ K := by dsimp[K,rowWordBudget,StoredAttachment.wordBudget,A];omega
  have scale_width : (Code.ofRat scale.value).bits ≤ StoredServe.gridScalarBudget (2*h+1) L := by
    rw [StoredServe.gridScale_value]
    exact StoredServe.gridScalarBudget_scale budget ratio raw.2.2 (2*h+1) L budget_width ratio_width raw_bound
  have scale_A : (Code.ofRat scale.value).bits ≤ A := scale_width.trans (by dsimp[A,rowScalarBudget];omega)
  have literal : (Code.ofRat 16).bits = 8 := by decide
  have radius_A : (Code.ofRat radius.value).bits ≤ A := by
    have actual := ratDiv_result_bits scale.value 16
    rw [literal] at actual
    dsimp only[radius,ratDiv_value]
    dsimp[A,rowScalarBudget]
    omega
  have weight_inputs (v : Fin n) : (Code.ofRat weights.value[v.val]).bits+1 ≤ W := by
    have actual := Weights.mixedCell_bits buying physical (emptyState input).value allowance[raw.1.val] scale.value v A (by omega)
      (fun v => (buying_width v).trans LA) (fun v => (physical_width v).trans LA) ((allowance_width raw.1).trans LA) scale_A
    simpa only [weights,Weights.mixed,Weights.materialize_get,W] using Nat.add_le_add_right actual 1
  have labels (v : Fin n) : Runtime.ShortestPath.width distances.value[v.val] ≤ R := by
    rw [Runtime.ShortestPath.iterate_value]
    exact Runtime.ShortestPath.iterate_label_width encoded weights.value origin n W (by dsimp[W];omega) weight_inputs v
  have label_B (v : Fin n) : Runtime.ShortestPath.width distances.value[v.val] ≤ B := (labels v).trans (by dsimp[B];omega)
  have buy_B (v : Fin n) : (Code.ofRat buying[v.val]).bits ≤ B := (buying_width v).trans (LA.trans (by dsimp[B];omega))
  have radius_B : (Code.ofRat radius.value).bits ≤ B := radius_A.trans (by dsimp[B];omega)
  have row_trace := (rowFromDistances_words buying radius.value mate distances.value B (by dsimp[B];omega) buy_B radius_B label_B).mono
    (show 12*B+40+n ≤ K by dsimp[K,rowWordBudget,B,A,R];nlinarith)
  have weights_trace := (Weights.mixed_words buying physical (emptyState input).value allowance[raw.1.val] scale.value A (by omega)
    (fun v => (buying_width v).trans LA) (fun v => (physical_width v).trans LA) ((allowance_width raw.1).trans LA) scale_A).mono
    (show 22*A+56+n ≤ K by dsimp[K,rowWordBudget,StoredAttachment.wordBudget,A];omega)
  have distance_trace := (Runtime.ShortestPath.iterate_words encoded weights.value origin n W (by dsimp[W];omega) weight_inputs).mono
    (show 2*(W+Runtime.ShortestPath.labelBudget n W)+9+n+n ≤ K by
      dsimp[K,rowWordBudget,StoredAttachment.wordBudget,W,A];omega)
  have scale_trace := (StoredServe.gridScale_words budget ratio raw.2.2 L budget_width).mono (show
      4*L+2*(ratio.size+1)*(raw.2.2.val+1)+60 ≤ K by
    have product := Nat.mul_le_mul (Nat.add_le_add_right ratio_width 1) (Nat.add_le_add_right raw_bound 1)
    have inputB : StoredServe.gridScalarBudget (2*h+1) L ≤ K := by dsimp[K,rowWordBudget,StoredAttachment.wordBudget,A,rowScalarBudget];omega
    unfold StoredServe.gridScalarBudget at inputB
    nlinarith)
  have empty_trace := emptyState_words input K ni one
  have encoding_trace := Queries.encodingEvents_words K ni one
  have radius_trace : WordsWithin K radius.events := by
    intro event member word present
    have actual := ratDiv_words scale.value 16 event member word present
    rw [literal] at actual
    have AK : A ≤ K := by dsimp[K,rowWordBudget,StoredAttachment.wordBudget,A];omega
    dsimp[A,rowScalarBudget] at *
    omega
  have ii := ((Nat.size_le.mpr Nat.lt_two_pow_self : raw.1.val.size ≤ raw.1.val).trans (Nat.le_of_lt raw.1.isLt)).trans hi
  have di := (Nat.size_le.mpr Nat.lt_two_pow_self : raw.2.2.val.size ≤ raw.2.2.val).trans (show raw.2.2.val ≤ K by omega)
  have oi := ((Nat.size_le.mpr Nat.lt_two_pow_self : origin.val.size ≤ origin.val).trans (Nat.le_of_lt origin.isLt)).trans ni
  have mi := ((Nat.size_le.mpr Nat.lt_two_pow_self : mate.val.size ≤ mate.val).trans (Nat.le_of_lt mate.isLt)).trans ni
  have allowance_K := (allowance_width raw.1).trans (LA.trans AK)
  refine ⟨?_,radius_A,?_⟩
  · simp only[materializeRow,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
      or_false,forall_eq_or_imp,forall_eq,and_true]
    aesop
  · intro v
    have actual := tollFromLabel_bits buying[v.val] radius.value distances.value[v.val] B (buy_B v) radius_B (label_B v)
    simpa only [materializeRow,rowFromDistances,Traced.bind_value,Weights.materialize_get,readRat,emit_value,Runtime.ShortestPath.read,
      rowTollBudget,B,A,R] using actual

end BuyAtBulk.Computation.Runtime.StoredCore
