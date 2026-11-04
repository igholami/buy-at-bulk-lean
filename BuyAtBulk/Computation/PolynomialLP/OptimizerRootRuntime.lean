import BuyAtBulk.Computation.PolynomialLP.OptimizationTrace

namespace BuyAtBulk.PolynomialLP
open Computation Computation.Runtime Rational ObjectiveRuntime InputTrace
variable {n m : ℕ}

def optimizerRootCount (n m B : ℕ) :=
  (m*n+m+n+1)*(6*(2*B+2)+30)+10+9+(m*(21*n+22)+5)+(10*n*n+42*n+6*m+10)

def optimizerRootValues (n m B : ℕ) : List ℕ :=
  [n,m,2,B,n+2,(n+2)*B,n*n,n*((n+2)*B),n*n+n*((n+2)*B),
    1,n*n+n*((n+2)*B)+1,2*(n*n+n*((n+2)*B)+1),2*(n*n+n*((n+2)*B)+1)+2]

def optimizerRootWords (n m B : ℕ) :=
  (64*(m+n+1)*(n+1)*(2*B+4)+64)+integerizeWordBudget n m B+
    boxedWordBudget n m ((n+2)*B+3)+(optimizerRootValues n m B).sum+64

theorem optimizerRoot_count (input : Stored (n:=n) (m:=m)) :
    (optimizerRoot input).events.length≤optimizerRootCount n m (inputBudget input) := by
  have budget := (inputBudgetTrace_runtime input).2.1
  have table := integerizeTrace_count input
  have boxed := boxedTrace_count (integerize input)
  simp only [optimizerRoot,Traced.bind_events,Traced.bind_value,inputBudgetTrace_value,
    InputTrace.addNat_value,mulNat_value,integerizeTrace_value,boxedTrace_value,
    List.length_append,InputTrace.addNat_count,mulNat_count,List.length_cons,List.length_nil]
  dsimp only [optimizerRootCount]
  omega

theorem optimizerRoot_words (input : Stored (n:=n) (m:=m)) :
    WordsWithin (optimizerRootWords n m (inputBudget input)) (optimizerRoot input).events := by
  let W := optimizerRootWords n m (inputBudget input)
  have budget := (inputBudgetTrace_runtime input).2.2.mono
    (show _≤W by dsimp only [W,optimizerRootWords]; omega)
  have table := (integerizeTrace_runtime input).2.2.mono
    (show _≤W by dsimp only [W,optimizerRootWords]; omega)
  have integral := integerized_bits input
  have boxed := (boxedTrace_words (integerize input) (integerL input+3) integral.1 integral.2).mono
    (show _≤W by dsimp only [W,optimizerRootWords,integerL]; omega)
  have width (value : ℕ) (member : value∈optimizerRootValues n m (inputBudget input)) : value.size≤W := by
    apply (Nat.size_le.mpr Nat.lt_two_pow_self).trans
    exact (List.single_le_sum (fun _ _ => Nat.zero_le _) _ member).trans
      (by dsimp only [W,optimizerRootWords]; omega)
  simp only [optimizerRoot,Traced.bind_events,Traced.bind_value,inputBudgetTrace_value,
    InputTrace.addNat_value,mulNat_value,integerizeTrace_value,boxedTrace_value,
    List.append_assoc,wordsWithin_append]
  refine ⟨budget,?_,?_,?_,?_,?_,?_,?_,?_,table,boxed,?_⟩
  all_goals
    simp only [InputTrace.addNat,mulNat,emit,wordsWithin_cons,wordsWithin_nil,List.mem_cons,
      List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
    repeat' apply And.intro
    all_goals
      apply width
      simp [optimizerRootValues]
end BuyAtBulk.PolynomialLP
