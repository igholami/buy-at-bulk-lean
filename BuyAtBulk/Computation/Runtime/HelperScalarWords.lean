import BuyAtBulk.Computation.Runtime.MaterializedHelper

namespace BuyAtBulk.Computation.Runtime.MaterializedHelper
open Rational BuyAtBulk.UpperBound
variable {n h ratio : ℕ}

def alphaWords (h : ℕ) := 8192*(h+1)^2+256

theorem alpha_words (h : ℕ) : WordsWithin (alphaWords h) (CoefficientPipeline.alpha h).events := by
  have hs : h.size≤h := Nat.size_le.mpr Nat.lt_two_pow_self
  have arg : (8*h).size≤8*h := Nat.size_le.mpr Nat.lt_two_pow_self
  have repeats := helperRepetitions_bound h
  have rs : (Nat.clog 2 (8*h)).size≤Nat.clog 2 (8*h) := Nat.size_le.mpr Nat.lt_two_pow_self
  have two : Nat.size 2=2 := by decide
  have eight : Nat.size 8=4 := by decide
  have large : 128*h+256≤alphaWords h := by unfold alphaWords; nlinarith
  have logarithm := (ceilingLog_words 2 (8*h) (8*h)).mono
    (show (Nat.size 2+(8*h).size+1)*(8*h+2)+2≤alphaWords h by
      rw [two]
      have product := Nat.mul_le_mul_right (8*h+2) (show (8*h).size+3≤8*h+3 by omega)
      unfold alphaWords
      nlinarith)
  have cast : (Code.ofRat (Nat.clog 2 (8*h) : ℚ)).bits≤8*h+3 := by
    rw [SourceCoefficients.natCast_bits]
    omega
  have c128 : (Code.ofRat (128:ℚ)).bits=11 := by decide
  have multiply := (wordBound_ratMul 128 (Nat.clog 2 (8*h) : ℚ)).mono
    (show 2*((Code.ofRat (128:ℚ)).bits+(Code.ofRat (Nat.clog 2 (8*h) : ℚ)).bits)+8≤alphaWords h by omega)
  simp only [CoefficientPipeline.alpha,Traced.bind_events,Traced.bind_value,natMul,emit_value,
    (helperLog_runtime h).1,ratCast,emit,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
    List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
  exact ⟨⟨by omega,by omega⟩,logarithm,by omega,multiply⟩

theorem factor_words (database : Core.RowDatabase h ratio n) (raw : Core.RawRow h ratio) (v : Fin n)
    (L K : ℕ) (constant : 5≤L) (indices : n+h+UpperBound.gridDepth h ratio+2≤K)
    (capacity : 12*L+105≤K)
    (toll : (Code.ofRat (Core.getRow database raw).toll[v.val]).bits≤L)
    (radius : (Code.ofRat (Core.getRow database raw).radius).bits≤L) :
    WordsWithin K (factor database raw v).events := by
  have negative (q : ℚ) : (Code.ofRat (-q)).bits=(Code.ofRat q).bits := by simp [Code.ofRat,Code.bits]
  have c1 : (Code.ofRat (1:ℚ)).bits=4 := by decide
  have c2 : (Code.ofRat (2:ℚ)).bits=5 := by decide
  have den := ratMul_result_bits 2 (Core.getRow database raw).radius
  have quotient := ratDiv_result_bits (Core.getRow database raw).toll[v.val] (2*(Core.getRow database raw).radius)
  have multiplied := (wordBound_ratMul 2 (Core.getRow database raw).radius).mono (show _≤K by omega)
  have divided := (wordBound_ratDiv (Core.getRow database raw).toll[v.val] (2*(Core.getRow database raw).radius)).mono (show _≤K by omega)
  have added : WordsWithin K (ratAdd 1 (-((Core.getRow database raw).toll[v.val]/(2*(Core.getRow database raw).radius)))).events := by
    intro event member word present
    have bound := ratAdd_words 1 (-((Core.getRow database raw).toll[v.val]/(2*(Core.getRow database raw).radius))) event member word present
    simp only [negative] at bound
    omega
  have vi : v.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have ri : raw.1.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := raw.1.isLt; omega)
  have di : raw.2.2.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := raw.2.2.isLt; omega)
  simp only [factor,Traced.bind_events,Traced.bind_value,Runtime.getRow,readRat,emit,emit_value,
    ratMul_value,ratDiv_value,negative,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
    List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
  repeat' apply And.intro
  all_goals first | exact multiplied | exact divided | exact added | omega

theorem isHeavy_words (opening : Vector ℚ n) (h : ℕ) (v : Fin n) (L K : ℕ)
    (constant : 5≤L) (indices : n≤K) (capacity : alphaWords h+4096*h+4*L+32≤K)
    (inputs : ∀ u : Fin n, (Code.ofRat opening[u.val]).bits≤L) :
    WordsWithin K (CoefficientPipeline.isHeavy opening h v).events := by
  have alpha := (alpha_words h).mono (show alphaWords h≤K by omega)
  have abits := SourceCoefficients.alpha_bits h
  have product := ratMul_result_bits (Core.helperAlpha h) opening[v.val]
  have input := inputs v
  have vi : v.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have c1 : (Code.ofRat (1:ℚ)).bits=4 := by decide
  have multiply := (wordBound_ratMul (Core.helperAlpha h) opening[v.val]).mono (show _≤K by omega)
  simp only [CoefficientPipeline.isHeavy,Traced.bind_events,Traced.bind_value,CoefficientPipeline.alpha_value,
    readRat,ratMul_value,ratLe,branch,emit,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
    List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
  exact ⟨alpha,⟨vi,by omega⟩,multiply,⟨by omega,by omega⟩,by omega⟩

theorem probability_words (opening : Vector ℚ n) (h : ℕ) (v : Fin n) (L K : ℕ)
    (constant : 5≤L) (indices : n≤K) (capacity : alphaWords h+4096*h+4*L+32≤K)
    (inputs : ∀ u : Fin n, (Code.ofRat opening[u.val]).bits≤L) :
    WordsWithin K (CoefficientPipeline.probability opening h v).events := by
  have heavy := isHeavy_words opening h v L K constant indices capacity inputs
  have alpha := (alpha_words h).mono (show alphaWords h≤K by omega)
  have abits := SourceCoefficients.alpha_bits h
  have input := inputs v
  have vi : v.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have multiply := (wordBound_ratMul (Core.helperAlpha h) opening[v.val]).mono (show _≤K by omega)
  simp only [CoefficientPipeline.probability,Traced.bind_events,Traced.bind_value]
  split
  · simp only [Traced.pure_events,wordsWithin_append,wordsWithin_nil,and_true]
    exact heavy
  · simp only [Traced.bind_events,Traced.bind_value,CoefficientPipeline.alpha_value,readRat,emit,
      wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,
      forall_eq_or_imp,forall_eq,and_true]
    exact ⟨heavy,alpha,⟨vi,by omega⟩,multiply⟩

theorem heavyScan_words (opening : Vector ℚ n) (h : ℕ) (vertices : List (Fin n)) (L K : ℕ)
    (constant : 5≤L) (indices : n≤K) (capacity : alphaWords h+4096*h+4*L+32≤K)
    (inputs : ∀ u : Fin n, (Code.ofRat opening[u.val]).bits≤L) :
    WordsWithin K (CoefficientPipeline.heavyScan opening h vertices).events := by
  induction vertices with
  | nil => simp [CoefficientPipeline.heavyScan,Traced.pure]
  | cons v rest ih =>
    have heavy := isHeavy_words opening h v L K constant indices capacity inputs
    have vi : v.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
    simp only [CoefficientPipeline.heavyScan,Traced.bind_events,Traced.bind_value,emit_value]
    split <;> simp only [Traced.pure_events,emit,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
      List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
    all_goals aesop

end BuyAtBulk.Computation.Runtime.MaterializedHelper
