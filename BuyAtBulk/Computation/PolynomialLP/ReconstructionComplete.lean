import BuyAtBulk.Computation.PolynomialLP.ReconstructionRuntime
import BuyAtBulk.Computation.PolynomialLP.InputTrace

/-! Complete reconstruction instrumentation: binary-length computation and
materialization of the finite candidate index list are charged explicitly. -/
namespace BuyAtBulk.PolynomialLP.ReconstructionRuntime
open Computation.Runtime Computation.Rational

def indexValues {F : ℕ} : List (Fin F) → Traced (List ℕ)
  | [] => Traced.pure []
  | i::rest => do
      let v ← emit .read [i.val.size] i.val
      let tail ← indexValues rest
      emit .cons [v.size] (v::tail)

@[simp] theorem indexValues_value {F : ℕ} (indices : List (Fin F)) :
    (indexValues indices).value=indices.map Fin.val := by
  induction indices with
  | nil => rfl
  | cons i rest ih => simp [indexValues,Traced.bind_value,ih]

@[simp] theorem indexValues_count {F : ℕ} (indices : List (Fin F)) :
    (indexValues indices).events.length=2*indices.length := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
    simp only [indexValues,Traced.bind_events,Traced.bind_value,List.length_append,emit_length,emit_value,ih,List.length_cons]
    omega

theorem indexValues_words {F : ℕ} (indices : List (Fin F)) (K : ℕ) (bound : F≤K) :
    WordsWithin K (indexValues indices).events := by
  induction indices with
  | nil => simp [indexValues,Traced.pure]
  | cons i rest ih =>
    have word : i.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
    simpa [indexValues,Traced.bind_events,Traced.bind_value,emit,wordsWithin_append,wordsWithin_cons,
      wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp] using And.intro word (And.intro ih word)

def reconstructComplete (lo hi : ℚ) (D : ℕ) : Traced (Option ℚ) := do
  let denominator ← emit .read [lo.den.size] lo.den
  let bits ← InputTrace.bitLength denominator
  let twice ← natMul 2 bits
  let length ← emit .natAdd [twice.size,1,(twice+1).size] (twice+1)
  let indices ← indexList length
  let indices ← indexValues indices
  let list ← candidates lo indices
  find lo hi D list

@[simp] theorem reconstructComplete_value (lo hi : ℚ) (D : ℕ) :
    (reconstructComplete lo hi D).value=PolynomialLP.reconstruct lo hi D := by
  simp [reconstructComplete,Traced.bind_value,InputTrace.bitLength_value,natMul,emit,
    PolynomialLP.reconstruct,reconstructionCandidates]

theorem reconstructComplete_count (lo hi : ℚ) (D : ℕ) :
    (reconstructComplete lo hi D).events.length≤
      (2*lo.den.size+1)*(44*lo.den.size+23)+6*lo.den.size+8 := by
  have indices (F : ℕ) : (List.finRange F).map Fin.val=List.range F := by simp
  have candidate := candidates_count lo (List.range (2*lo.den.size+1)) (2*lo.den.size)
    (fun i member => Nat.le_of_lt_succ (List.mem_range.mp member))
  simp only [List.length_range] at candidate
  have finish := find_count lo hi D (candidates lo (List.range (2*lo.den.size+1))).value
  simp only [candidates_value,List.length_map,List.length_range] at finish
  simp only [reconstructComplete,Traced.bind_events,Traced.bind_value,List.length_append,emit_length,
    emit_value,InputTrace.bitLength_count,InputTrace.bitLength_value,natMul,emit,indexList_value,
    indexList_count,indexValues_value,indexValues_count,List.length_finRange,indices,List.length_cons,List.length_nil,candidates_value]
  nlinarith

theorem reconstructComplete_words (lo hi : ℚ) (D B : ℕ)
    (input : (Code.ofRat lo).Bounded B) (upper : (Code.ofRat hi).bits≤2*B+2) :
    WordsWithin (wordBudget (2*B) B+D.size+8) (reconstructComplete lo hi D).events := by
  let K := wordBudget (2*B) B+D.size+8
  have den : lo.den.size≤B := by
    apply Nat.size_le.mpr
    simpa only [Code.ofRat,Int.natAbs_natCast] using input.2
  have capacity : 2*B+4≤K := by unfold K wordBudget; nlinarith
  have indices (F : ℕ) : (List.finRange F).map Fin.val=List.range F := by simp
  have core : WordsWithin K ((candidates lo (List.range (2*lo.den.size+1))).events++
      (find lo hi D (candidates lo (List.range (2*lo.den.size+1))).value).events) :=
    (reconstruct_words lo hi D B input upper).mono (by unfold K wordBudget; nlinarith)
  have sizewords : WordsWithin K (InputTrace.bitLength lo.den).events :=
    (InputTrace.bitLength_words lo.den).mono (by omega)
  have listwords : WordsWithin K (indexList (2*lo.den.size+1)).events :=
    indexList_words _ _ (by omega)
  have mapwords := indexValues_words (List.finRange (2*lo.den.size+1)) K (by omega)
  have twoSize : Nat.size 2=2 := by decide
  have s : lo.den.size.size≤lo.den.size := Nat.size_le.mpr Nat.lt_two_pow_self
  have twice : (2*lo.den.size).size≤2*lo.den.size := Nat.size_le.mpr Nat.lt_two_pow_self
  have next : (2*lo.den.size+1).size≤2*lo.den.size+1 := Nat.size_le.mpr Nat.lt_two_pow_self
  simp only [wordsWithin_append] at core
  simp only [reconstructComplete,Traced.bind_events,Traced.bind_value,emit_value,InputTrace.bitLength_value,
    natMul,indexList_value,indexValues_value,indices,emit,wordsWithin_append,wordsWithin_cons,
    wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true,twoSize]
  repeat' apply And.intro
  all_goals first | exact sizewords | exact listwords | exact mapwords | exact core.1 | exact core.2 | omega

/-- Complete candidate scheduling and reconstruction, including computation of
its binary length and allocation of every index and candidate list cell. -/
theorem reconstructComplete_runtime (lo hi : ℚ) (D B : ℕ)
    (input : (Code.ofRat lo).Bounded B) (upper : (Code.ofRat hi).bits≤2*B+2) :
    (reconstructComplete lo hi D).value=PolynomialLP.reconstruct lo hi D ∧
    (reconstructComplete lo hi D).events.length≤(2*B+1)*(44*B+23)+6*B+8 ∧
    WordsWithin (wordBudget (2*B) B+D.size+8) (reconstructComplete lo hi D).events := by
  have den : lo.den.size≤B := by
    apply Nat.size_le.mpr
    simpa only [Code.ofRat,Int.natAbs_natCast] using input.2
  refine ⟨reconstructComplete_value lo hi D,?_,reconstructComplete_words lo hi D B input upper⟩
  have actual := reconstructComplete_count lo hi D
  nlinarith [Nat.mul_le_mul (show 2*lo.den.size+1≤2*B+1 by omega)
    (show 44*lo.den.size+23≤44*B+23 by omega)]

end BuyAtBulk.PolynomialLP.ReconstructionRuntime
