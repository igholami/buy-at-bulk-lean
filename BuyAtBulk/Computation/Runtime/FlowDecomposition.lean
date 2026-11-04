import BuyAtBulk.Computation.Runtime.FlowExtractWords

namespace BuyAtBulk.Computation.Runtime.FlowExtract
open Rational
variable {n : ℕ} (input : Computation.ShortestPath.GraphEncoding n)

def decompose (matrix : FlowDecomposition.FlowMatrix n) (source target : Fin n) :
    Traced (Option (FlowDecomposition.WeightedPaths input.graph source target)) := do
  let square ← natMul n n
  let fuel ← emit .natAdd [square.size,1,(square+1).size] (square+1)
  extract input source target fuel matrix 1

@[simp] theorem decompose_value (matrix : FlowDecomposition.FlowMatrix n) (source target : Fin n) :
    (decompose input matrix source target).value=FlowDecomposition.decompose input.graph (Equiv.refl _) matrix source target := by
  simp [decompose,Traced.bind_value,natMul,FlowDecomposition.decompose]

theorem decompose_count (matrix : FlowDecomposition.FlowMatrix n) (source target : Fin n) :
    (decompose input matrix source target).events.length≤(n*n+1)*stepBudget n+6 := by
  have extracted := extract_count input source target (n*n+1) matrix 1
  simp only [decompose,Traced.bind_events,Traced.bind_value,natMul,emit_value,emit_length,List.length_append]
  omega

theorem denominatorBits_bound (matrix : FlowDecomposition.FlowMatrix n) (L : ℕ)
    (cells : ∀ u v : Fin n, (Code.ofRat matrix[u.val][v.val]).bits≤L) :
    FlowDecomposition.denominatorInputBits matrix≤n*n*L := by
  unfold FlowDecomposition.denominatorInputBits
  calc
    _ ≤ ∑ _ : Fin n × Fin n, L := by
      apply Finset.sum_le_sum
      intro index _
      have bound := cells index.1 index.2
      simp only [Code.ofRat,Code.bits,Int.natAbs_natCast] at bound
      change (matrix[index.1.val][index.2.val]).den.size≤L
      omega
    _ = _ := by simp

def decompositionWords (n L : ℕ) : ℕ := n+(n*n+1)+8*(2*(n*n*L+1)+4)+64

/-- Complete operation and word bounds refer to the actual stored-matrix
program, including the search, bottleneck, residuals and returned sparse list. -/
theorem decompose_words (matrix : FlowDecomposition.FlowMatrix n) (source target : Fin n) (L : ℕ)
    (cells : ∀ u v : Fin n, (Code.ofRat matrix[u.val][v.val]).bits≤L)
    (nonnegative : ∀ u v : Fin n, 0≤matrix[u.val][v.val])
    (unit : ∀ u v : Fin n, matrix[u.val][v.val]≤1)
    (nonedge : ∀ u v : Fin n, ¬input.graph.Adj u v → matrix[u.val][v.val]=0)
    (balance : ∀ v : Fin n, (∑ u : Fin n, matrix[v.val][u.val])-(∑ u : Fin n, matrix[u.val][v.val])=
      (if source=v then 1 else 0)-(if target=v then 1 else 0)) :
    WordsWithin (decompositionWords n L) (decompose input matrix source target).events := by
  let D := FlowDecomposition.commonDenominator matrix
  have Dpos : 0<D := FlowDecomposition.commonDenominator_pos matrix
  have initial : FlowDecomposition.StateValid input.graph (Equiv.refl _) source target D matrix 1 :=
    ⟨by norm_num,le_rfl,by change (1:ℕ)∣D; exact one_dvd _,nonnegative,unit,
      FlowDecomposition.decoded_coordinate_denominator (Equiv.refl _) matrix,nonedge,by simpa [FlowDecomposition.decodedFlow,FlowDecomposition.matrixFlow] using balance⟩
  have bits : D.size≤n*n*L+1 := (FlowDecomposition.commonDenominator_bits matrix).trans
    (Nat.add_le_add_right (denominatorBits_bound matrix L cells) 1)
  have inner := (extract_words input source target D (n*n+1) (n*n+1) matrix 1 Dpos le_rfl initial).mono
    (show wordBudget n D (n*n+1)≤decompositionWords n L by dsimp [wordBudget,decompositionWords]; omega)
  have nsize : n.size≤decompositionWords n L := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by unfold decompositionWords; omega)
  have square : (n*n).size≤decompositionWords n L := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by unfold decompositionWords; omega)
  have next : (n*n+1).size≤decompositionWords n L := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by unfold decompositionWords; omega)
  have one : 1≤decompositionWords n L := by unfold decompositionWords; omega
  simpa only [decompose,Traced.bind_events,Traced.bind_value,natMul,emit,wordsWithin_append,
    wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true] using
    And.intro (And.intro nsize nsize) (And.intro (And.intro square (And.intro one next)) inner)

end BuyAtBulk.Computation.Runtime.FlowExtract
