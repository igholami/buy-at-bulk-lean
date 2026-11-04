import BuyAtBulk.Computation.Runtime.RoundingRefinement
import BuyAtBulk.Computation.Runtime.RoundingCost
import BuyAtBulk.Computation.Runtime.RoundingWords
import BuyAtBulk.Computation.Runtime.OptimizedParameterWords

namespace BuyAtBulk.Computation.Runtime.StoredRounding
open BuyAtBulk.UpperBound
open Rational
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)


theorem optimized_parameter_bounds (h : ℕ) : Optimization.scaleRatio h≤2*h+10 ∧ Optimization.r h≤4*h+4 := by
  have qBound : Optimization.q h≤2*h+2 := by rw[←Parameters.q_eq];exact Parameters.q_bound h
  have root := OptimizedParameters.ceilSqrt_le_self (Optimization.q h)
  constructor
  · unfold Optimization.scaleRatio
    rw[←Parameters.ceilSqrt_eq]
    exact max_le (by omega) (by omega)
  · unfold Optimization.r
    omega


def optimized (buying physical opening : Vector ℚ n) (budget : ℚ) (source target : Vector (Fin n) h) (lengths : Vector ℚ h) :
    Traced (Option (Output input source target)) :=
  let parameters := OptimizedParameters.compute h
  have admissible : 2≤parameters.value.ratio := by
    simp only[parameters,OptimizedParameters.compute_value]
    exact (by decide : 2≤8).trans (Optimization.scaleRatio_lower h)
  let answer := run input buying physical opening budget source target lengths parameters.value.ratio parameters.value.girth admissible
  ⟨answer.value,parameters.events++answer.events⟩


theorem optimized_value (buying physical opening : Vector ℚ n) (budget : ℚ) (source target : Vector (Fin n) h) (lengths : Vector ℚ h) :
    (optimized input buying physical opening budget source target lengths).value.map (decodeOutput input source target)=
      Rounding.run input.graph (Equiv.refl _) (fun v => buying[v.val]) (fun v => physical[v.val]) (fun v => opening[v.val]) budget
        (fun i => source[i.val]) (fun i => target[i.val]) (fun i => lengths[i.val]) (Optimization.scaleRatio h) (Optimization.r h) := by
  simp only[optimized]
  rw[run_value]
  simp only[OptimizedParameters.compute_value]


def optimizedCount (n h : ℕ) := OptimizedParameters.count h+roundingCount n h


theorem optimized_count (buying physical opening : Vector ℚ n) (budget : ℚ) (source target : Vector (Fin n) h) (lengths : Vector ℚ h) :
    (optimized input buying physical opening budget source target lengths).events.length≤optimizedCount n h := by
  have parameter := OptimizedParameters.compute_count h
  simp only[optimized,List.length_append]
  have rounded := run_count input buying physical opening budget source target lengths
    (OptimizedParameters.compute h).value.ratio (OptimizedParameters.compute h).value.girth
    (by simp only[OptimizedParameters.compute_value];exact (by decide : 2≤8).trans (Optimization.scaleRatio_lower h))
  exact Nat.add_le_add parameter rounded


def optimizedInputBudget (h L : ℕ) := L+4*h+16

def optimizedWords (n h L : ℕ) := OptimizedParameters.wordBudget h+roundingWords n h (optimizedInputBudget h L)


theorem optimized_words (buying physical opening : Vector ℚ n) (budget : ℚ) (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (L : ℕ) (constant : 8≤L)
    (buying_width : ∀ v : Fin n, (Code.ofRat buying[v.val]).bits≤L)
    (physical_width : ∀ v : Fin n, (Code.ofRat physical[v.val]).bits≤L)
    (opening_width : ∀ v : Fin n, (Code.ofRat opening[v.val]).bits≤L)
    (budget_width : (Code.ofRat budget).bits≤L) (lengths_width : ∀ i : Fin h, (Code.ofRat lengths[i.val]).bits≤L) :
    WordsWithin (optimizedWords n h L) (optimized input buying physical opening budget source target lengths).events := by
  let K := optimizedWords n h L
  let S := optimizedInputBudget h L
  have LS : L≤S := by dsimp[S,optimizedInputBudget];omega
  have lower : 2≤(OptimizedParameters.compute h).value.ratio := by
    simp only[OptimizedParameters.compute_value]
    exact (by decide : 2≤8).trans (Optimization.scaleRatio_lower h)
  have bounds := optimized_parameter_bounds h
  have ratio_width : (OptimizedParameters.compute h).value.ratio.size≤S := by
    simp only[OptimizedParameters.compute_value]
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[S,optimizedInputBudget];omega)
  have girth_width : (OptimizedParameters.compute h).value.girth.size≤S := by
    simp only[OptimizedParameters.compute_value]
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[S,optimizedInputBudget];omega)
  have parameter := (OptimizedParameters.compute_words h).mono
    (show OptimizedParameters.wordBudget h≤K by dsimp[K,optimizedWords];omega)
  have rounded := (run_words input buying physical opening budget source target lengths
    (OptimizedParameters.compute h).value.ratio (OptimizedParameters.compute h).value.girth lower S (by omega)
    (fun v => (buying_width v).trans LS) (fun v => (physical_width v).trans LS) (fun v => (opening_width v).trans LS)
    (budget_width.trans LS) (fun i => (lengths_width i).trans LS) ratio_width girth_width).mono
    (show roundingWords n h S≤K by dsimp[K,optimizedWords,S];omega)
  simpa only[optimized,wordsWithin_append] using And.intro parameter rounded

end BuyAtBulk.Computation.Runtime.StoredRounding
