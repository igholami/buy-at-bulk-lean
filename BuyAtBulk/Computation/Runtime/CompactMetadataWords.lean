import BuyAtBulk.Computation.Runtime.CompactMetadata

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.Computation.Runtime.CompactLift
open Rational BuyAtBulk.PolynomialLP.CompactEncoding
variable {n h : ℕ}

def lengthsWords (n h L : ℕ) := h+n+commodityWords n h L+allowanceBits n L+30

theorem lengths_words (input : ShortestPath.GraphEncoding n) (f : CompactFlow.Solution input.graph h)
    (point : Vector ℚ (variableCount n h)) (coordinates : f.coordinates=decode (fun j=>point[j.val]))
    (L : ℕ) (constant : 5 ≤ L)
    (pointBits : ∀ j : Fin (variableCount n h),(Code.ofRat point[j.val]).bits+1 ≤ L)
    (physicalBits : ∀ v : Fin n,(Code.ofRat (f.physical v)).bits+1 ≤ L) :
    WordsWithin (lengthsWords n h L)
      (lengths input (Vector.ofFn f.physical) (Vector.ofFn f.source) (Vector.ofFn f.target) point).events := by
  let K := lengthsWords n h L
  let options := Weights.materialize (commodity input (Vector.ofFn f.physical) (Vector.ofFn f.source) (Vector.ofFn f.target) point) optionWidth
  have values (i : Fin h) : options.value[i.val]=some (FlowDecomposition.fractionalLength input.graph (Equiv.refl _) f i) := by
    simp only [options,Weights.materialize_get,commodity_value input f point coordinates]
  have bounds (i : Fin h) := fractionalLength_bits input f point coordinates i L constant pointBits physicalBits
  have optionWords : WordsWithin K options.events := by
    apply Weights.materialize_words
    · dsimp[K,lengthsWords];omega
    · intro i
      exact (commodity_words input f point coordinates i L constant pointBits physicalBits).mono
        (by dsimp[K,lengthsWords];omega)
    · intro i
      rw [commodity_value input f point coordinates]
      simp only [optionWidth]
      have bound := bounds i
      dsimp[K,lengthsWords]
      omega
  have indices := indexList_words h K (by dsimp[K,lengthsWords];omega)
  have checked := completeScan_words options.value (List.finRange h) K
    (by dsimp[K,lengthsWords];omega) (by dsimp[K,lengthsWords];omega)
  have payload (valid : ∀ i : Fin h,options.value[i.val].isSome=true) :
      WordsWithin K (collectPayload options.value valid).events := by
    apply collectPayload_words _ _ (allowanceBits n L) K
    · dsimp[K,lengthsWords];omega
    · dsimp[K,lengthsWords];omega
    · intro i
      rw [Option.get_of_eq_some _ (values i)]
      exact bounds i
  have one : 1 ≤ K := by dsimp[K,lengthsWords];omega
  have hi : h.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[K,lengthsWords];omega)
  unfold lengths
  dsimp only
  split <;> simp only [indexList_value,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
    List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
  all_goals aesop

end BuyAtBulk.Computation.Runtime.CompactLift
