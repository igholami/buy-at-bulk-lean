import BuyAtBulk.Computation.Runtime.HelperSumWords

namespace BuyAtBulk.Computation.Runtime.MaterializedHelper
open Rational BuyAtBulk.UpperBound
variable {n h ratio : ℕ}

def coefficientCapacity (n h L : ℕ) : ℕ :=
  alphaWords h+8192*h+128*L+2*sumBudget n (4*L+8)+256

theorem helperLog_words (h : ℕ) :
    WordsWithin (alphaWords h) (ceilingLog 2 (8*h) (8*h)).events := by
  have all := alpha_words h
  simp only [CoefficientPipeline.alpha,Traced.bind_events,Traced.bind_value,natMul,emit_value,wordsWithin_append] at all
  exact all.2.1

theorem amplitude_words (opening : Vector ℚ n) (database : Core.RowDatabase h ratio n)
    (raw : Core.RawRow h ratio) (L K : ℕ) (constant : 5≤L)
    (indices : n+h+UpperBound.gridDepth h ratio+2≤K) (capacity : coefficientCapacity n h L≤K)
    (inputs : ∀ v : Fin n, (Code.ofRat opening[v.val]).bits≤L)
    (tolls : ∀ v : Fin n, (Code.ofRat (Core.getRow database raw).toll[v.val]).bits≤L)
    (radius : (Code.ofRat (Core.getRow database raw).radius).bits≤L) :
    WordsWithin K (CoefficientPipeline.amplitude opening database raw).events := by
  have C := capacity
  unfold coefficientCapacity at C
  have heavy := heavyScan_words opening h (List.finRange n) L K constant (by omega) (by omega) inputs
  let vertices := (CoefficientPipeline.heavyScan opening h (List.finRange n)).value
  have length : vertices.length≤n := by
    dsimp only [vertices]
    rw [CoefficientPipeline.heavyScan_value]
    simpa using List.length_filter_le (fun v : Fin n => decide (1≤Core.helperAlpha h*opening[v.val])) (List.finRange n)
  have sum := weightedTolls_words opening database raw vertices n L K constant length indices (by omega) inputs tolls
  have sum_bits := weightedTolls_bits opening database raw vertices n L constant length inputs tolls
  have c3 : (Code.ofRat (3:ℚ)).bits=5 := by decide
  have c8 : (Code.ofRat (8:ℚ)).bits=7 := by decide
  have numerator := ratMul_result_bits 3 (Core.getRow database raw).radius
  have threshold := ratDiv_result_bits (3*(Core.getRow database raw).radius) 8
  have multiply := (wordBound_ratMul 3 (Core.getRow database raw).radius).mono (show _≤K by omega)
  have divide := (wordBound_ratDiv (3*(Core.getRow database raw).radius) 8).mono (show _≤K by omega)
  have vi : n≤K := by omega
  have ri : raw.1.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := raw.1.isLt; omega)
  have di : raw.2.2.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := raw.2.2.isLt; omega)
  have eightSize : Nat.size 8=4 := by decide
  have sixteenSize : Nat.size 16=5 := by decide
  have hs : h.size≤h := Nat.size_le.mpr Nat.lt_two_pow_self
  have repeats := helperRepetitions_bound h
  have rs : (Nat.clog 2 (8*h)).size≤Nat.clog 2 (8*h) := Nat.size_le.mpr Nat.lt_two_pow_self
  have exponent : 16*Nat.clog 2 (8*h)≤128*h := by omega
  have powerbits : (2^(16*Nat.clog 2 (8*h))).size≤128*h+1 := by rw [Nat.size_pow]; omega
  have log := (helperLog_words h).mono (show alphaWords h≤K by omega)
  have power := (helperPower_runtime h).2.2.mono (show 128*h+2≤K by omega)
  have indices_words := indexList_words n K vi
  let program : Traced ℚ := do
    let argument ← natMul 8 h
    let repetitions ← ceilingLog 2 argument (8*h)
    let exponent ← natMul 16 repetitions
    let power ← powerTwo exponent
    ratCast power
  have phase : WordsWithin K program.events := by
    simp only [program,Traced.bind_events,Traced.bind_value,natMul,emit_value,
      (helperLog_runtime h).1,powerTwo_value,ratCast,emit,wordsWithin_append,
      wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,
      forall_eq_or_imp,forall_eq,and_true]
    repeat' apply And.intro
    all_goals first | exact log | exact power | (norm_num <;> omega)
  have either (test : Bool) : WordsWithin K (if test then program else Traced.pure 0).events := by
    cases test
    · simp [Traced.pure]
    · exact phase
  dsimp only [vertices] at sum sum_bits
  simp only [CoefficientPipeline.amplitude,Traced.bind_events,Traced.bind_value,indexList_value,
    Runtime.getRow,readRat,ratMul_value,ratDiv_value,ratLess,branch,emit_value,wordsWithin_append]
  simp only [emit,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,
    forall_eq_or_imp,forall_eq,and_true]
  repeat' apply And.intro
  all_goals first | exact indices_words | exact heavy | exact sum | exact multiply | exact divide | exact either _ | omega

end BuyAtBulk.Computation.Runtime.MaterializedHelper
