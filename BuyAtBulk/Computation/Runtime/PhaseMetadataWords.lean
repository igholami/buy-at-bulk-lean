import BuyAtBulk.Computation.Runtime.PhaseMetadata

namespace BuyAtBulk.Computation.Runtime.StoredRounding
open BuyAtBulk.UpperBound
open Rational
variable {n h : ℕ}

def phaseScalarBudget (L : ℕ) := 4*L+100

theorem raisedOpening_bits (buying opening : Vector ℚ n) (L : ℕ)
    (inputs : ∀ v : Fin n, (Code.ofRat opening[v.val]).bits ≤ L) (v : Fin n) :
    (Code.ofRat (raisedOpening buying opening).value[v.val]).bits ≤ phaseScalarBudget L := by
  rw[raisedOpening_get]
  unfold Rounding.raisedOpening
  split_ifs
  · have literal : (Code.ofRat 1).bits=4 := by decide
    rw[literal];unfold phaseScalarBudget;omega
  · exact (inputs v).trans (by unfold phaseScalarBudget;omega)

theorem raisedOpening_words (buying opening : Vector ℚ n) (L : ℕ)
    (buying_width : ∀ v : Fin n, (Code.ofRat buying[v.val]).bits ≤ L)
    (opening_width : ∀ v : Fin n, (Code.ofRat opening[v.val]).bits ≤ L) :
    WordsWithin (n+phaseScalarBudget L) (raisedOpening buying opening).events := by
  let K := n+phaseScalarBudget L
  have ni : n ≤ K := by dsimp[K];omega
  have one : 1 ≤ K := by dsimp[K,phaseScalarBudget];omega
  apply Weights.materialize_words _ _ K ni
  · intro v
    have vi := ((Nat.size_le.mpr Nat.lt_two_pow_self : v.val.size ≤ v.val).trans (Nat.le_of_lt v.isLt)).trans ni
    have buy := (buying_width v).trans (show L ≤ K by dsimp[K,phaseScalarBudget];omega)
    have opening := (opening_width v).trans (show L ≤ K by dsimp[K,phaseScalarBudget];omega)
    have literal : (Code.ofRat 1).bits=4 := by decide
    simp only[raisedCell,Traced.bind_events,Traced.bind_value,readRat,emit_value,zeroTest,branch]
    split_ifs <;>simp only[wordsWithin_append,emit,literal,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
      or_false,forall_eq_or_imp,forall_eq,and_true]
    all_goals dsimp[K,phaseScalarBudget] at *;aesop <;>omega
  · intro v
    have actual := raisedOpening_bits buying opening L opening_width v
    simpa only[raisedOpening,Weights.materialize_get] using actual.trans (show phaseScalarBudget L ≤ K by dsimp[K];omega)

theorem zeroTarget_words (source target : Vector (Fin n) h) (lengths : Vector ℚ h) (L : ℕ)
    (inputs : ∀ i : Fin h, (Code.ofRat lengths[i.val]).bits ≤ L) :
    WordsWithin (n+h+phaseScalarBudget L) (zeroTarget source target lengths).events := by
  let K := n+h+phaseScalarBudget L
  have ni : n ≤ K := by dsimp[K];omega
  have hi : h ≤ K := by dsimp[K];omega
  have one : 1 ≤ K := by dsimp[K,phaseScalarBudget];omega
  have scalar : L ≤ K := by dsimp[K,phaseScalarBudget];omega
  have fin_width (v : Fin n) : v.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans ((Nat.le_of_lt v.isLt).trans ni)
  apply Weights.materialize_words _ _ K hi
  · intro i
    have ii := ((Nat.size_le.mpr Nat.lt_two_pow_self : i.val.size ≤ i.val).trans (Nat.le_of_lt i.isLt)).trans hi
    have qi := (inputs i).trans scalar
    have source_width := fin_width source[i.val]
    have target_width := fin_width target[i.val]
    simp only[targetCell,Traced.bind_events,Traced.bind_value,readRat,emit_value,zeroTest,branch]
    split_ifs <;>simp only[wordsWithin_append,emit,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
      or_false,forall_eq_or_imp,forall_eq,and_true] <;>dsimp[K,phaseScalarBudget] at * <;>aesop <;>omega
  · intro i
    exact fin_width _

theorem activeFlags_words (lengths : Vector ℚ h) (positive : Bool) (L : ℕ)
    (inputs : ∀ i : Fin h, (Code.ofRat lengths[i.val]).bits ≤ L) :
    WordsWithin (h+phaseScalarBudget L) (activeFlags lengths positive).events := by
  let K := h+phaseScalarBudget L
  have hi : h ≤ K := by dsimp[K];omega
  have one : 1 ≤ K := by dsimp[K,phaseScalarBudget];omega
  apply Weights.materialize_words _ _ K hi
  · intro i
    have ii := ((Nat.size_le.mpr Nat.lt_two_pow_self : i.val.size ≤ i.val).trans (Nat.le_of_lt i.isLt)).trans hi
    have qi := (inputs i).trans (show L ≤ K by dsimp[K,phaseScalarBudget];omega)
    simp only[activeCell,Traced.bind_events,Traced.bind_value,readRat,emit_value,zeroTest,wordsWithin_append,
      emit,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
    dsimp[K,phaseScalarBudget] at *
    aesop <;>omega
  · intro i
    exact one

theorem allowance_bits (lengths : Vector ℚ h) (L : ℕ) (inputs : ∀ i : Fin h, (Code.ofRat lengths[i.val]).bits ≤ L) (i : Fin h) :
    (Code.ofRat (allowance lengths).value[i.val]).bits ≤ phaseScalarBudget L := by
  rw[allowance_get]
  unfold Rounding.allowance
  split_ifs
  · have literal : (Code.ofRat 1).bits=4 := by decide
    rw[literal];unfold phaseScalarBudget;omega
  · have actual := ratMul_result_bits 64 lengths[i.val]
    have literal : (Code.ofRat 64).bits=10 := by decide
    rw[literal] at actual
    have width := inputs i
    change (Code.ofRat (64*lengths[i.val])).bits ≤ phaseScalarBudget L
    unfold phaseScalarBudget
    omega

theorem allowance_words (lengths : Vector ℚ h) (L : ℕ) (inputs : ∀ i : Fin h, (Code.ofRat lengths[i.val]).bits ≤ L) :
    WordsWithin (h+phaseScalarBudget L) (allowance lengths).events := by
  let K := h+phaseScalarBudget L
  have hi : h ≤ K := by dsimp[K];omega
  have one : 1 ≤ K := by dsimp[K,phaseScalarBudget];omega
  apply Weights.materialize_words _ _ K hi
  · intro i
    have ii := ((Nat.size_le.mpr Nat.lt_two_pow_self : i.val.size ≤ i.val).trans (Nat.le_of_lt i.isLt)).trans hi
    have qi := (inputs i).trans (show L ≤ K by dsimp[K,phaseScalarBudget];omega)
    have literal : (Code.ofRat 1).bits=4 := by decide
    have product : WordsWithin K (ratMul 64 lengths[i.val]).events := by
      intro event member word present
      have actual := ratMul_words 64 lengths[i.val] event member word present
      have sixtyfour : (Code.ofRat 64).bits=10 := by decide
      rw[sixtyfour] at actual
      have width := inputs i
      dsimp[K,phaseScalarBudget]
      omega
    simp only[allowanceCell,Traced.bind_events,Traced.bind_value,readRat,emit_value,zeroTest,branch]
    split_ifs <;>simp only[wordsWithin_append,emit,literal,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
      or_false,forall_eq_or_imp,forall_eq,and_true] <;>dsimp[K,phaseScalarBudget] at * <;>aesop <;>omega
  · intro i
    have actual := allowance_bits lengths L inputs i
    simpa only[allowance,Weights.materialize_get] using actual.trans (show phaseScalarBudget L ≤ K by dsimp[K];omega)

theorem constantVector_words {α : Type} (m : ℕ) (a : α) (width : ℕ) :
    WordsWithin (m+width+1) (constantVector m a width).events := by
  apply Weights.materialize_words _ _ _ (by omega)
  · intro i
    simp[emit,WordsWithin]
    omega
  · intro i
    omega

def binaryDepthWords (h : ℕ) := (2*h+4)*(2*h+4)+10

theorem binaryDepth_words (h : ℕ) : WordsWithin (binaryDepthWords h) (binaryDepth h).events := by
  let K := binaryDepthWords h
  have hi : h.size ≤ h := Nat.size_le.mpr Nat.lt_two_pow_self
  have ti : (2*h).size ≤ 2*h := Nat.size_le.mpr Nat.lt_two_pow_self
  have log := (ceilingLog_words 2 (2*h) (2*h)).mono (show ((2 : ℕ).size+(2*h).size+1)*(2*h+2)+2 ≤ K by
    rw[show (2 : ℕ).size=2 by decide]
    dsimp[K,binaryDepthWords]
    nlinarith)
  simp only[binaryDepth,Traced.bind_events,Traced.bind_value,emit_value,emit,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
    List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
  dsimp[K,binaryDepthWords] at *
  exact ⟨⟨by nlinarith,by nlinarith,by nlinarith⟩,log⟩

end BuyAtBulk.Computation.Runtime.StoredRounding
