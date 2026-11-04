import BuyAtBulk.Computation.PolynomialLP.Words.Matrix

/-! A stored finite dot product with an actual charged index list. -/
set_option autoImplicit false
namespace BuyAtBulk.Computation.Runtime.ArrayDot
open Rational
variable {n : ℕ}

def run (a b : Vector ℚ n) : Traced ℚ :=
  let indices := indexList n
  let result := PolynomialLP.dotScan a b indices.value
  ⟨result.value,indices.events++result.events⟩

@[simp] theorem run_value (a b : Vector ℚ n) :
    (run a b).value=∑ v : Fin n,a[v.val]*b[v.val] := by
  simp only [run,PolynomialLP.dotScan_value,indexList_value,Fin.sum_univ_def]

theorem run_count (a b : Vector ℚ n) : (run a b).events.length=10*n := by
  simp only [run,List.length_append,indexList_count,PolynomialLP.dotScan_count,indexList_value,List.length_finRange]
  omega

def wordBudget (n L : ℕ) := n+PolynomialLP.Trace.dotWordBudget n n L+4

theorem run_words (a b : Vector ℚ n) (L : ℕ) (constant : 5 ≤ L)
    (aBits : ∀ v : Fin n,(Code.ofRat a[v.val]).bits+1 ≤ L)
    (bBits : ∀ v : Fin n,(Code.ofRat b[v.val]).bits+1 ≤ L) :
    WordsWithin (wordBudget n L) (run a b).events := by
  have indices := indexList_words n (wordBudget n L) (by dsimp[wordBudget];omega)
  have sum := (PolynomialLP.Trace.dotScan_words a b (List.finRange n) L constant aBits bBits).mono
    (show _ ≤ wordBudget n L by simp only [List.length_finRange];dsimp[wordBudget];omega)
  simpa only [run,indexList_value,wordsWithin_append] using And.intro indices sum

theorem run_bits (a b : Vector ℚ n) (L : ℕ) (constant : 5 ≤ L)
    (aBits : ∀ v : Fin n,(Code.ofRat a[v.val]).bits+1 ≤ L)
    (bBits : ∀ v : Fin n,(Code.ofRat b[v.val]).bits+1 ≤ L) :
    (Code.ofRat (run a b).value).bits ≤ 2*(4*n+1)*L+2 := by
  have sum := PolynomialLP.Trace.dotScan_bits a b (List.finRange n) L constant aBits bBits
  simpa only [run,indexList_value,List.length_finRange] using sum

end BuyAtBulk.Computation.Runtime.ArrayDot
