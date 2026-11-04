import BuyAtBulk.Computation.Runtime.HelperSumWords

namespace BuyAtBulk.Computation.Runtime.MaterializedHelper
open Rational BuyAtBulk.UpperBound
variable {n h : ℕ}

theorem fixedCost_words (buying opening : Vector ℚ n) (h L K : ℕ)
    (constant : 5≤L) (indices : n≤K)
    (heavyCapacity : alphaWords h+4096*h+4*L+32≤K)
    (sumCapacity : 2*(L+sumBudget n L)+8≤K)
    (buyingbits : ∀ v : Fin n, (Code.ofRat buying[v.val]).bits≤L)
    (openingbits : ∀ v : Fin n, (Code.ofRat opening[v.val]).bits≤L) :
    WordsWithin K (fixedCost buying opening h).events := by
  have order := indexList_words n K indices
  have heavy := heavyScan_words opening h (List.finRange n) L K constant indices heavyCapacity openingbits
  have length : (CoefficientPipeline.heavyScan opening h (List.finRange n)).value.length≤n := by
    rw [CoefficientPipeline.heavyScan_value]
    simpa using List.length_filter_le (fun v : Fin n => decide (1≤Core.helperAlpha h*opening[v.val])) (List.finRange n)
  have sum := buyingSum_words buying (CoefficientPipeline.heavyScan opening h (List.finRange n)).value
    n L K constant length indices sumCapacity buyingbits
  simpa only [fixedCost,Traced.bind_events,Traced.bind_value,indexList_value,wordsWithin_append] using
    And.intro order (And.intro heavy sum)

theorem normalization_words (budget : ℚ) (h L K : ℕ)
    (capacity : alphaWords h+8192*h+4*L+128≤K) (budgetbits : (Code.ofRat budget).bits≤L) :
    WordsWithin K (normalization budget h).events := by
  have alpha := (alpha_words h).mono (show alphaWords h≤K by omega)
  have abits := SourceCoefficients.alpha_bits h
  have c4 : (Code.ofRat (4:ℚ)).bits=6 := by decide
  have firstbits := ratMul_result_bits 4 (Core.helperAlpha h)
  have first := (wordBound_ratMul 4 (Core.helperAlpha h)).mono (show _≤K by omega)
  have second := (wordBound_ratMul (4*Core.helperAlpha h) budget).mono (show _≤K by omega)
  simpa only [normalization,Traced.bind_events,Traced.bind_value,CoefficientPipeline.alpha_value,
    ratMul_value,wordsWithin_append] using And.intro alpha (And.intro first second)

end BuyAtBulk.Computation.Runtime.MaterializedHelper
