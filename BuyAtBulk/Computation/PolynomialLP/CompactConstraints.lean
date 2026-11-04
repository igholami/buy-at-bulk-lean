import BuyAtBulk.Computation.PolynomialLP.CompactIndices

set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP.CompactTrace
open Computation Computation.Runtime

def addNat (a b : ℕ) : Traced ℕ := emit .natAdd [a.size,b.size,(a+b).size] (a+b)

@[simp] theorem constraints_box (n h : ℕ) (upper : Bool) (c : CompactFlow.VariableIndex (Fin n) h) :
    CompactEncoding.constraints n h (.inl (upper,c))=
      finSumFinEquiv (.inl (finProdFinEquiv (finTwoEquiv.symm upper,CompactEncoding.variableEquiv n h c))) := rfl
@[simp] theorem constraints_node (n h : ℕ) (iv : Fin h × Fin n) :
    CompactEncoding.constraints n h (.inr (.inl iv))=
      finSumFinEquiv (.inr (finSumFinEquiv (.inl (finProdFinEquiv iv)))) := rfl
@[simp] theorem constraints_balance (n h : ℕ) (positive incoming : Bool) (iv : Fin h × Fin n) :
    CompactEncoding.constraints n h (.inr (.inr (.inl ((positive,incoming),iv))))=
      (finSumFinEquiv <| Sum.inr <| finSumFinEquiv <| Sum.inr <| finSumFinEquiv <| Sum.inl <|
        finProdFinEquiv (finProdFinEquiv (finTwoEquiv.symm positive,finTwoEquiv.symm incoming),finProdFinEquiv iv)) := rfl
@[simp] theorem constraints_arc (n h : ℕ) (i : Fin h) (uv : Fin n × Fin n) :
    CompactEncoding.constraints n h (.inr (.inr (.inr (i,uv))))=
      (finSumFinEquiv <| Sum.inr <| finSumFinEquiv <| Sum.inr <| finSumFinEquiv <| Sum.inr <|
        finProdFinEquiv (i,finProdFinEquiv uv)) := rfl

def constraintIndex (n h : ℕ) (r : Fin (CompactEncoding.constraintCount n h)) :
    Traced (CompactFlow.ConstraintIndex (Fin n) h) :=
  let nc := natMul h n
  let sq := natMul n n
  let tc := natMul h sq.value
  let both := addNat nc.value tc.value
  let nv := addNat n both.value
  let bc := natMul 4 nc.value
  let inner := addNat bc.value tc.value
  let right := addNat nc.value inner.value
  let box := natMul 2 nv.value
  let tag := sumIndex box.value right.value r
  let result : Traced (CompactFlow.ConstraintIndex (Fin n) h) :=
    match tag.value with
    | .inl k => do
        let pair ← productIndex 2 nv.value k
        let upper ← boolIndex pair.1
        let c ← variableIndex n h pair.2
        emit .cons [1] (.inl (upper,c))
    | .inr k =>
        let tag := sumIndex nc.value inner.value k
        match tag.value with
        | .inl k => do
            let iv ← productIndex h n k
            emit .cons [iv.1.val.size,iv.2.val.size] (.inr (.inl iv))
        | .inr k =>
            let tag := sumIndex bc.value tc.value k
            match tag.value with
            | .inl k => do
                let pair ← productIndex 4 nc.value k
                let bits ← productIndex 2 2 pair.1
                let positive ← boolIndex bits.1
                let incoming ← boolIndex bits.2
                let iv ← productIndex h n pair.2
                emit .cons [1,1,iv.1.val.size,iv.2.val.size] (.inr (.inr (.inl ((positive,incoming),iv))))
            | .inr k => do
                let pair ← productIndex h sq.value k
                let uv ← productIndex n n pair.2
                emit .cons [pair.1.val.size,uv.1.val.size,uv.2.val.size] (.inr (.inr (.inr (pair.1,uv))))
  ⟨result.value,nc.events++sq.events++tc.events++both.events++nv.events++bc.events++inner.events++
    right.events++box.events++tag.events++result.events⟩

theorem sumIndex_encode (a b : ℕ) (i : Fin (a+b)) :
    finSumFinEquiv (sumIndex a b i).value=i := by
  rw [sumIndex_value,Equiv.apply_symm_apply]

theorem constraint_value (n h : ℕ) (r : Fin (CompactEncoding.constraintCount n h)) :
    (constraintIndex n h r).value=(CompactEncoding.constraints n h).symm r := by
  apply (CompactEncoding.constraints n h).injective
  rw [Equiv.apply_symm_apply]
  dsimp only [constraintIndex,natMul,addNat,emit]
  have root_enc := sumIndex_encode (2*(n+(h*n+h*(n*n)))) (h*n+(4*(h*n)+h*(n*n))) r
  cases root : (sumIndex (2*(n+(h*n+h*(n*n)))) (h*n+(4*(h*n)+h*(n*n))) r).value with
  | inl k =>
    rw [root] at root_enc
    simp only [Traced.bind_value,productIndex_value,boolIndex_value,variable_value,emit_value]
    rw [constraints_box,Equiv.apply_symm_apply,Equiv.symm_apply_apply]
    simp only [Prod.eta]
    change finSumFinEquiv (Sum.inl ((@finProdFinEquiv 2 (n+(h*n+h*(n*n))))
      ((@finProdFinEquiv 2 (n+(h*n+h*(n*n)))).symm k)))=r
    rw [Equiv.apply_symm_apply]
    exact root_enc
  | inr k =>
    rw [root] at root_enc
    have node_enc := sumIndex_encode (h*n) (4*(h*n)+h*(n*n)) k
    cases node : (sumIndex (h*n) (4*(h*n)+h*(n*n)) k).value with
    | inl iv =>
      rw [node] at node_enc
      simp only [node,Traced.bind_value,productIndex_value,emit_value]
      rw [constraints_node,Equiv.apply_symm_apply,node_enc]
      exact root_enc
    | inr rest =>
      rw [node] at node_enc
      simp only [node]
      have kind_enc := sumIndex_encode (4*(h*n)) (h*(n*n)) rest
      cases kind : (sumIndex (4*(h*n)) (h*(n*n)) rest).value with
      | inl balance =>
        rw [kind] at kind_enc
        simp only [kind,Traced.bind_value,productIndex_value,boolIndex_value,emit_value]
        rw [constraints_balance]
        simp only [Equiv.symm_apply_apply,Prod.eta,Equiv.apply_symm_apply]
        rw [kind_enc,node_enc]
        exact root_enc
      | inr arc =>
        rw [kind] at kind_enc
        simp only [kind,Traced.bind_value,productIndex_value,emit_value]
        rw [constraints_arc]
        simp only [Prod.eta,Equiv.apply_symm_apply]
        rw [kind_enc,node_enc]
        exact root_enc

theorem boolIndex_words (i : Fin 2) (K : ℕ) (capacity : 3≤K) : WordsWithin K (boolIndex i).events := by
  have width : i.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := i.isLt;omega)
  simp only [boolIndex,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
    or_false,forall_eq_or_imp,forall_eq,and_true]
  omega

theorem constraint_count (n h : ℕ) (r : Fin (CompactEncoding.constraintCount n h)) :
    (constraintIndex n h r).events.length≤64 := by
  have first := sumIndex_count (2*(n+(h*n+h*(n*n)))) (h*n+(4*(h*n)+h*(n*n))) r
  dsimp only [constraintIndex,natMul,addNat,emit]
  cases root : (sumIndex (2*(n+(h*n+h*(n*n)))) (h*n+(4*(h*n)+h*(n*n))) r).value with
  | inl k =>
    have selected := variable_count n h (productIndex 2 (n+(h*n+h*(n*n))) k).value.2
    simp only [Traced.bind_events,Traced.bind_value,productIndex_count,boolIndex_count,
      List.length_append,List.length_cons,List.length_nil,emit_length]
    omega
  | inr k =>
    have second := sumIndex_count (h*n) (4*(h*n)+h*(n*n)) k
    cases node : (sumIndex (h*n) (4*(h*n)+h*(n*n)) k).value with
    | inl iv =>
      simp only [node,Traced.bind_events,Traced.bind_value,productIndex_count,List.length_append,
        List.length_cons,List.length_nil,emit_length]
      omega
    | inr rest =>
      simp only [node]
      have third := sumIndex_count (4*(h*n)) (h*(n*n)) rest
      cases kind : (sumIndex (4*(h*n)) (h*(n*n)) rest).value with
      | inl balance =>
        simp only [kind,Traced.bind_events,Traced.bind_value,productIndex_count,boolIndex_count,
          List.length_append,List.length_cons,List.length_nil,emit_length]
        omega
      | inr arc =>
        simp only [kind,Traced.bind_events,Traced.bind_value,productIndex_count,
          List.length_append,List.length_cons,List.length_nil,emit_length]
        omega

def indexBudget (n h : ℕ) :=
  32*(n+h+n*n+CompactEncoding.variableCount n h+CompactEncoding.constraintCount n h+16)

theorem constraint_words (n h : ℕ) (r : Fin (CompactEncoding.constraintCount n h)) (K : ℕ)
    (capacity : indexBudget n h≤K) : WordsWithin K (constraintIndex n h r).events := by
  have limit : n+h+n*n+CompactEncoding.variableCount n h+CompactEncoding.constraintCount n h+16≤K := by
    unfold indexBudget at capacity
    omega
  have base : n+h+n*n+h*n+h*(n*n)+16≤K := by
    dsimp only [CompactEncoding.variableCount,CompactEncoding.constraintCount] at limit
    omega
  have one : 1≤K := by omega
  have three : 3≤K := by omega
  have ns : n.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have hs : h.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have sq : (n*n).size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have nc : (h*n).size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have tc : (h*(n*n)).size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have both : (h*n+h*(n*n)).size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have nv : (n+(h*n+h*(n*n))).size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have bc : (4*(h*n)).size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by
    dsimp only [CompactEncoding.variableCount,CompactEncoding.constraintCount] at limit;omega)
  have inner : (4*(h*n)+h*(n*n)).size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by
    dsimp only [CompactEncoding.variableCount,CompactEncoding.constraintCount] at limit;omega)
  have right : (h*n+(4*(h*n)+h*(n*n))).size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by
    dsimp only [CompactEncoding.variableCount,CompactEncoding.constraintCount] at limit;omega)
  have box : (2*(n+(h*n+h*(n*n)))).size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by
    dsimp only [CompactEncoding.variableCount,CompactEncoding.constraintCount] at limit;omega)
  have four : Nat.size 4≤K := by
    have c : Nat.size 4=3 := by decide
    omega
  have two : Nat.size 2≤K := by
    have c : Nat.size 2=2 := by decide
    omega
  have first := sumIndex_words (2*(n+(h*n+h*(n*n)))) (h*n+(4*(h*n)+h*(n*n))) r K (by
    dsimp only [CompactEncoding.variableCount,CompactEncoding.constraintCount] at limit;omega)
  dsimp only [constraintIndex,natMul,addNat,emit]
  cases root : (sumIndex (2*(n+(h*n+h*(n*n)))) (h*n+(4*(h*n)+h*(n*n))) r).value with
  | inl k =>
    have pair := productIndex_words 2 (n+(h*n+h*(n*n))) k K (by
      dsimp only [CompactEncoding.variableCount,CompactEncoding.constraintCount] at limit;omega)
    have bool := boolIndex_words (productIndex 2 (n+(h*n+h*(n*n))) k).value.1 K three
    have selected := variable_words n h (productIndex 2 (n+(h*n+h*(n*n))) k).value.2 K base
    simp only [Traced.bind_events,Traced.bind_value,emit,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
      List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
    aesop
  | inr k =>
    have second := sumIndex_words (h*n) (4*(h*n)+h*(n*n)) k K (by
      dsimp only [CompactEncoding.variableCount,CompactEncoding.constraintCount] at limit;omega)
    cases node : (sumIndex (h*n) (4*(h*n)+h*(n*n)) k).value with
    | inl iv =>
      have pair := productIndex_words h n iv K (by omega)
      have i : (productIndex h n iv).value.1.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans
        (by have := (productIndex h n iv).value.1.isLt;omega)
      have v : (productIndex h n iv).value.2.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans
        (by have := (productIndex h n iv).value.2.isLt;omega)
      simp only [node,Traced.bind_events,Traced.bind_value,emit,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
        List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
      aesop
    | inr rest =>
      simp only [node]
      have third := sumIndex_words (4*(h*n)) (h*(n*n)) rest K (by
        dsimp only [CompactEncoding.variableCount,CompactEncoding.constraintCount] at limit;omega)
      cases kind : (sumIndex (4*(h*n)) (h*(n*n)) rest).value with
      | inl balance =>
        have pair := productIndex_words 4 (h*n) balance K (by
          dsimp only [CompactEncoding.variableCount,CompactEncoding.constraintCount] at limit;omega)
        have bits := productIndex_words 2 2 (productIndex 4 (h*n) balance).value.1 K (by omega)
        have positive := boolIndex_words (productIndex 2 2 (productIndex 4 (h*n) balance).value.1).value.1 K three
        have incoming := boolIndex_words (productIndex 2 2 (productIndex 4 (h*n) balance).value.1).value.2 K three
        have iv := productIndex_words h n (productIndex 4 (h*n) balance).value.2 K (by omega)
        have i : (productIndex h n (productIndex 4 (h*n) balance).value.2).value.1.val.size≤K :=
          (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := (productIndex h n (productIndex 4 (h*n) balance).value.2).value.1.isLt;omega)
        have v : (productIndex h n (productIndex 4 (h*n) balance).value.2).value.2.val.size≤K :=
          (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := (productIndex h n (productIndex 4 (h*n) balance).value.2).value.2.isLt;omega)
        simp only [kind,Traced.bind_events,Traced.bind_value,emit,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
          List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
        aesop
      | inr arc =>
        have pair := productIndex_words h (n*n) arc K (by omega)
        have uv := productIndex_words n n (productIndex h (n*n) arc).value.2 K (by omega)
        have i : (productIndex h (n*n) arc).value.1.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans
          (by have := (productIndex h (n*n) arc).value.1.isLt;omega)
        have u : (productIndex n n (productIndex h (n*n) arc).value.2).value.1.val.size≤K :=
          (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := (productIndex n n (productIndex h (n*n) arc).value.2).value.1.isLt;omega)
        have v : (productIndex n n (productIndex h (n*n) arc).value.2).value.2.val.size≤K :=
          (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := (productIndex n n (productIndex h (n*n) arc).value.2).value.2.isLt;omega)
        simp only [kind,Traced.bind_events,Traced.bind_value,emit,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,
          List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
        aesop

end BuyAtBulk.PolynomialLP.CompactTrace
