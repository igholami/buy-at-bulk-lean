import BuyAtBulk.Computation.PolynomialLP.CompactEncoding

/-! Concrete sum/product finite-index decoding. Integer quotient and remainder
are explicit instructions; no finite-numbering callback is supplied. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP.CompactTrace
open Computation Computation.Runtime

def sumIndex (a b : ℕ) (i : Fin (a+b)) : Traced (Fin a ⊕ Fin b) :=
  let before : List Event := [⟨.natCompare,[i.val.size,a.size]⟩,⟨.branch,[1]⟩]
  if left : i.val<a then
    ⟨.inl ⟨i.val,left⟩,before++[⟨.write,[i.val.size]⟩]⟩
  else
    ⟨.inr ⟨i.val-a,by have := i.isLt;omega⟩,before++
      [⟨.natSub,[i.val.size,a.size,(i.val-a).size]⟩,⟨.write,[(i.val-a).size]⟩]⟩

@[simp] theorem sumIndex_value (a b : ℕ) (i : Fin (a+b)) :
    (sumIndex a b i).value=finSumFinEquiv.symm i := by
  apply Fin.addCases (motive:=fun i => (sumIndex a b i).value=finSumFinEquiv.symm i) _ _ i
  · intro j
    simp [sumIndex,j.isLt]
  · intro j
    simp [sumIndex]

theorem sumIndex_count (a b : ℕ) (i : Fin (a+b)) : (sumIndex a b i).events.length≤4 := by
  simp only [sumIndex]
  split <;> simp

theorem sumIndex_words (a b : ℕ) (i : Fin (a+b)) (K : ℕ) (capacity : a+b+2≤K) :
    WordsWithin K (sumIndex a b i).events := by
  have one : 1≤K := by omega
  have ib : i.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := i.isLt;omega)
  have ab : a.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have sb : (i.val-a).size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := i.isLt;omega)
  simp only [sumIndex]
  split <;> simp only [wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
    or_false,forall_eq_or_imp,forall_eq,and_true] <;> aesop

def productIndex (a b : ℕ) (i : Fin (a*b)) : Traced (Fin a × Fin b) :=
  let quotient := i.divNat
  let remainder := i.modNat
  ⟨(quotient,remainder),[⟨.read,[i.val.size]⟩,
    ⟨.intDiv,[i.val.size,b.size,quotient.val.size]⟩,
    ⟨.natMod,[i.val.size,b.size,remainder.val.size]⟩,
    ⟨.write,[quotient.val.size,remainder.val.size]⟩]⟩

@[simp] theorem productIndex_value (a b : ℕ) (i : Fin (a*b)) :
    (productIndex a b i).value=finProdFinEquiv.symm i := rfl
@[simp] theorem productIndex_count (a b : ℕ) (i : Fin (a*b)) : (productIndex a b i).events.length=4 := rfl

theorem productIndex_words (a b : ℕ) (i : Fin (a*b)) (K : ℕ) (capacity : a*b+b+2≤K) :
    WordsWithin K (productIndex a b i).events := by
  have ib : i.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := i.isLt;omega)
  have bb : b.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have qb : i.divNat.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans
    ((Nat.div_le_self i.val b).trans (by have := i.isLt;omega))
  have rb : i.modNat.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans
    ((Nat.mod_le i.val b).trans (by have := i.isLt;omega))
  simp only [productIndex,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
    or_false,forall_eq_or_imp,forall_eq,and_true]
  aesop

def boolIndex (i : Fin 2) : Traced Bool :=
  ⟨finTwoEquiv i,[⟨.natCompare,[i.val.size,0]⟩,⟨.branch,[1]⟩]⟩
@[simp] theorem boolIndex_value (i : Fin 2) : (boolIndex i).value=finTwoEquiv i := rfl
@[simp] theorem boolIndex_count (i : Fin 2) : (boolIndex i).events.length=2 := rfl

def variableIndex (n h : ℕ) (j : Fin (CompactEncoding.variableCount n h)) : Traced (CompactFlow.VariableIndex (Fin n) h) :=
  let nc := natMul h n
  let sq := natMul n n
  let tc := natMul h sq.value
  let right := emit .natAdd [nc.value.size,tc.value.size,(nc.value+tc.value).size] (nc.value+tc.value)
  let tag := sumIndex n right.value j
  let result : Traced (CompactFlow.VariableIndex (Fin n) h) :=
    match tag.value with
    | .inl v => emit .cons [v.val.size] (.inl v)
    | .inr j =>
      let tag := sumIndex nc.value tc.value j
      match tag.value with
      | .inl k => do
          let iv ← productIndex h n k
          emit .cons [iv.1.val.size,iv.2.val.size] (.inr (.inl iv))
      | .inr k => do
          let pair ← productIndex h sq.value k
          let uv ← productIndex n n pair.2
          emit .cons [pair.1.val.size,uv.1.val.size,uv.2.val.size] (.inr (.inr (pair.1,uv)))
  ⟨result.value,nc.events++sq.events++tc.events++right.events++tag.events++result.events⟩

theorem variable_value (n h : ℕ) (j : Fin (CompactEncoding.variableCount n h)) :
    (variableIndex n h j).value=(CompactEncoding.variableEquiv n h).symm j := by
  apply (CompactEncoding.variableEquiv n h).injective
  rw [Equiv.apply_symm_apply]
  dsimp only [variableIndex,natMul,emit]
  simp only [sumIndex_value]
  cases root : (finSumFinEquiv.symm j : Fin n ⊕ Fin (h*n+h*(n*n))) with
  | inl v =>
    simp only [root,emit_value]
    change finSumFinEquiv (Sum.inl v)=j
    rw [← root]
    exact finSumFinEquiv.apply_symm_apply j
  | inr k =>
    simp only [root]
    cases inner : (finSumFinEquiv.symm k : Fin (h*n) ⊕ Fin (h*(n*n))) with
    | inl iv =>
      simp only [inner,Traced.bind_value,productIndex_value,emit_value]
      change finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inl (finProdFinEquiv (finProdFinEquiv.symm iv)))))=j
      rw [Equiv.apply_symm_apply,← inner,Equiv.apply_symm_apply,← root,Equiv.apply_symm_apply]
    | inr iuv =>
      simp only [inner,Traced.bind_value,productIndex_value,emit_value]
      change finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inr (finProdFinEquiv
        ((finProdFinEquiv.symm iuv).1,finProdFinEquiv (finProdFinEquiv.symm (finProdFinEquiv.symm iuv).2))))))=j
      rw [Equiv.apply_symm_apply]
      simp only [Prod.eta,Equiv.apply_symm_apply]
      rw [← inner,Equiv.apply_symm_apply,← root,Equiv.apply_symm_apply]

theorem variable_count (n h : ℕ) (j : Fin (CompactEncoding.variableCount n h)) :
    (variableIndex n h j).events.length≤24 := by
  have first := sumIndex_count n (h*n+h*(n*n)) j
  dsimp only [variableIndex,natMul,emit]
  cases root : (sumIndex n (h*n+h*(n*n)) j).value with
  | inl v =>
    simp only [root,List.length_append,List.length_cons,List.length_nil]
    omega
  | inr k =>
    have second := sumIndex_count (h*n) (h*(n*n)) k
    cases inner : (sumIndex (h*n) (h*(n*n)) k).value with
    | inl iv =>
      simp only [root,inner,Traced.bind_events,Traced.bind_value,productIndex_count,emit_length,
        List.length_append,List.length_cons,List.length_nil]
      omega
    | inr iuv =>
      simp only [root,inner,Traced.bind_events,Traced.bind_value,productIndex_count,emit_length,
        List.length_append,List.length_cons,List.length_nil]
      omega

theorem variable_words (n h : ℕ) (j : Fin (CompactEncoding.variableCount n h)) (K : ℕ)
    (capacity : n+h+n*n+h*n+h*(n*n)+16≤K) :
    WordsWithin K (variableIndex n h j).events := by
  have ns : n.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have hs : h.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have square : (n*n).size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have nodes : (h*n).size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have arcs : (h*(n*n)).size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have right : (h*n+h*(n*n)).size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have first := sumIndex_words n (h*n+h*(n*n)) j K (by omega)
  dsimp only [variableIndex,natMul,emit]
  cases root : (sumIndex n (h*n+h*(n*n)) j).value with
  | inl v =>
    have vi : v.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := v.isLt;omega)
    simp only [root,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
      or_false,forall_eq_or_imp,forall_eq,and_true]
    aesop
  | inr k =>
    have second := sumIndex_words (h*n) (h*(n*n)) k K (by omega)
    cases inner : (sumIndex (h*n) (h*(n*n)) k).value with
    | inl iv =>
      have pair := productIndex_words h n iv K (by omega)
      have i : (productIndex h n iv).value.1.val.size≤K :=
        (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := (productIndex h n iv).value.1.isLt;omega)
      have v : (productIndex h n iv).value.2.val.size≤K :=
        (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := (productIndex h n iv).value.2.isLt;omega)
      simp only [root,inner,Traced.bind_events,Traced.bind_value,emit,wordsWithin_append,wordsWithin_cons,
        wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
      aesop
    | inr iuv =>
      have pair := productIndex_words h (n*n) iuv K (by omega)
      have uv := productIndex_words n n (productIndex h (n*n) iuv).value.2 K (by omega)
      have i : (productIndex h (n*n) iuv).value.1.val.size≤K :=
        (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := (productIndex h (n*n) iuv).value.1.isLt;omega)
      have u : (productIndex n n (productIndex h (n*n) iuv).value.2).value.1.val.size≤K :=
        (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := (productIndex n n (productIndex h (n*n) iuv).value.2).value.1.isLt;omega)
      have v : (productIndex n n (productIndex h (n*n) iuv).value.2).value.2.val.size≤K :=
        (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := (productIndex n n (productIndex h (n*n) iuv).value.2).value.2.isLt;omega)
      simp only [root,inner,Traced.bind_events,Traced.bind_value,emit,wordsWithin_append,wordsWithin_cons,
        wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
      aesop

end BuyAtBulk.PolynomialLP.CompactTrace
