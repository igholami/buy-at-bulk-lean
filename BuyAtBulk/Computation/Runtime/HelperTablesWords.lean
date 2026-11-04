import BuyAtBulk.Computation.Runtime.HelperAmplitudeWords
import BuyAtBulk.Computation.Runtime.HelperFixedWords

namespace BuyAtBulk.Computation.Runtime.MaterializedHelper
open Rational BuyAtBulk.UpperBound
variable {n h ratio m : ℕ}

def tableWords (n h m L : ℕ) := coefficientCapacity n h L+n+m+3*h+8

theorem tables_words (buying opening : Vector ℚ n) (budget : ℚ)
    (database : Core.RowDatabase h ratio n) (rows : Vector (Core.RawRow h ratio) m)
    (L : ℕ) (constant : 5≤L) (ratio_ge : 2≤ratio)
    (buyingbits : ∀ v : Fin n, (Code.ofRat buying[v.val]).bits≤L)
    (openingbits : ∀ v : Fin n, (Code.ofRat opening[v.val]).bits≤L)
    (budgetbits : (Code.ofRat budget).bits≤L)
    (radii : ∀ r : Fin m, (Code.ofRat (Core.getRow database rows[r.val]).radius).bits≤L)
    (tolls : ∀ r : Fin m, ∀ v : Fin n, (Code.ofRat (Core.getRow database rows[r.val]).toll[v.val]).bits≤L) :
    WordsWithin (tableWords n h m L) (tables buying opening budget database rows).events := by
  let K := tableWords n h m L
  have C : coefficientCapacity n h L≤K := by dsimp [K,tableWords]; omega
  have big := C
  unfold coefficientCapacity at big
  have depth := Runtime.gridDepth_bound h ratio ratio_ge
  have indices : n+h+UpperBound.gridDepth h ratio+2≤K := by dsimp [K,tableWords]; omega
  have ni : n≤K := by omega
  have mi : m≤K := by dsimp [K,tableWords]; omega
  have nsize : n.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans ni
  have msize : m.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans mi
  have probability := Weights.materialize_words (CoefficientPipeline.probability opening h)
    (fun q => (Code.ofRat q).bits) K ni
    (fun v => probability_words opening h v L K constant ni (by omega) openingbits) (by
      intro v
      have value := SourceCoefficients.probability_bits (h:=h) opening v (L+1)
        (Nat.add_le_add_right (openingbits v) 1)
      rw [CoefficientPipeline.probability_value]
      omega)
  have factor_rows (r : Fin m) : WordsWithin K (Weights.materialize
      (factor database rows[r.val]) (fun q => (Code.ofRat q).bits)).events := by
    apply Weights.materialize_words _ _ _ ni
    · intro v
      exact factor_words database rows[r.val] v L K constant indices (by omega) (tolls r v) (radii r)
    · intro v
      have value := SourceCoefficients.factor_bits database rows[r.val] v (L+1)
        (Nat.add_le_add_right (tolls r v) 1) (Nat.add_le_add_right (radii r) 1)
      rw [factor_value]
      omega
  have factor_trace : WordsWithin K (factors database rows).events := by
    apply Weights.materialize_words _ _ _ mi
    · intro r
      have ri : r.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
      simpa only [Traced.bind_events,Traced.bind_value,emit,wordsWithin_append,wordsWithin_cons,
        wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true] using
        And.intro ri (factor_rows r)
    · intro r
      exact nsize
  have amplitude_trace : WordsWithin K (amplitudes opening database rows).events := by
    apply Weights.materialize_words _ _ _ mi
    · intro r
      have ri : r.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
      have amp := amplitude_words opening database rows[r.val] L K constant indices C openingbits (tolls r) (radii r)
      simpa only [Traced.bind_events,Traced.bind_value,emit,wordsWithin_append,wordsWithin_cons,
        wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true] using And.intro ri amp
    · intro r
      have value := SourceCoefficients.amplitude_bits opening database rows[r.val]
      simp only [Traced.bind_value,emit_value,CoefficientPipeline.amplitude_value]
      omega
  have smaller : sumBudget n L≤sumBudget n (4*L+8) := by unfold sumBudget; nlinarith
  have fixed := fixedCost_words buying opening h L K constant ni (by omega) (by omega) buyingbits openingbits
  have norm := normalization_words budget h L K (by omega) budgetbits
  have order := indexList_words m K mi
  simp only [tables,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
    or_false,forall_eq_or_imp,forall_eq,and_true]
  exact ⟨⟨⟨⟨⟨⟨order,probability⟩,factor_trace⟩,amplitude_trace⟩,fixed⟩,norm⟩,nsize,msize⟩

end BuyAtBulk.Computation.Runtime.MaterializedHelper
