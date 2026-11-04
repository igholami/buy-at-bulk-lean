import BuyAtBulk.Computation.Runtime.FlowUpdate

namespace BuyAtBulk.Computation.Runtime.FlowUpdate
open Rational
variable {n : ℕ} {G : SimpleGraph (Fin n)}

theorem minimum_bits (matrix : FlowDecomposition.FlowMatrix n) (mass : ℚ) {s t : Fin n}
    (walk : G.Walk s t) (L : ℕ) (massbits : (Code.ofRat mass).bits≤L)
    (cells : ∀ u v : Fin n, (Code.ofRat matrix[u.val][v.val]).bits≤L) :
    (Code.ofRat (minimum matrix mass walk).value).bits≤L := by
  induction walk with
  | nil => exact massbits
  | @cons s u t edge tail ih =>
    rw [minimum_cons]
    by_cases less : matrix[s.val][u.val]≤(minimum matrix mass tail).value
    · rw [min_eq_left less]; exact cells s u
    · rw [min_eq_right (le_of_not_ge less)]; exact ih

private theorem index_word (v : Fin n) (K : ℕ) (indices : n≤K) : v.val.size≤K :=
  (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)

theorem minimum_words (matrix : FlowDecomposition.FlowMatrix n) (mass : ℚ) {s t : Fin n}
    (walk : G.Walk s t) (K : ℕ) (indices : n≤K) (constant : 3≤K)
    (massbits : (Code.ofRat mass).bits≤K)
    (cells : ∀ u v : Fin n, (Code.ofRat matrix[u.val][v.val]).bits≤K) :
    WordsWithin K (minimum matrix mass walk).events := by
  have one : 1≤K := by omega
  have dimension : n.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans indices
  induction walk with
  | nil => simpa [minimum,emit,WordsWithin] using massbits
  | @cons s u t edge tail ih =>
    have si := index_word s K indices
    have ui := index_word u K indices
    have head := cells s u
    have rest := minimum_bits matrix mass tail K massbits cells
    have result := minimum_bits matrix mass (.cons edge tail) K massbits cells
    simp only [minimum,Traced.bind_events,Traced.bind_value,emit_value,readRat,ratLe,branch,
      wordsWithin_append,emit,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
      or_false,forall_eq_or_imp,forall_eq,and_true]
    by_cases less : matrix[s.val][u.val]≤(minimum matrix mass tail).value <;>
      simp only [less,decide_true,decide_false,Bool.true_eq,Bool.false_eq_true,ite_true,ite_false]
    all_goals aesop

theorem occurs_words (u v : Fin n) {s t : Fin n} (walk : G.Walk s t) (K : ℕ)
    (indices : n≤K) (one : 1≤K) : WordsWithin K (occurs u v walk).events := by
  have ui := index_word u K indices
  have vi := index_word v K indices
  induction walk with
  | nil => simp [occurs,WordsWithin,one]
  | @cons s w t edge tail ih =>
    have si := index_word s K indices
    have wi := index_word w K indices
    simp only [occurs]
    split <;> simp only [wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,
      List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
    all_goals aesop

theorem subtractCell_bits (matrix : FlowDecomposition.FlowMatrix n) (amount : ℚ) {s t : Fin n}
    (path : G.Path s t) (u v : Fin n) (L : ℕ) (constant : 3≤L)
    (amountbits : (Code.ofRat amount).bits≤L)
    (cells : ∀ u v : Fin n, (Code.ofRat matrix[u.val][v.val]).bits≤L) :
    (Code.ofRat (subtractCell matrix amount path u v).value).bits≤4*L+8 := by
  have negative (q : ℚ) : (Code.ofRat (-q)).bits=(Code.ofRat q).bits := by simp [Code.ofRat,Code.bits]
  have zero : (Code.ofRat (0:ℚ)).bits=3 := by decide
  have chosen : (Code.ofRat (if (occurs u v path.val).value then amount else 0)).bits≤L := by
    split <;> first | exact amountbits | simpa only [zero] using constant
  have result := ratAdd_result_bits matrix[u.val][v.val] (-(if (occurs u v path.val).value then amount else 0))
  simp only [negative] at result
  simp only [subtractCell,Traced.bind_value,emit_value,readRat,ratAdd_value]
  exact result.trans (by have head := cells u v; omega)

theorem subtractCell_words (matrix : FlowDecomposition.FlowMatrix n) (amount : ℚ) {s t : Fin n}
    (path : G.Path s t) (u v : Fin n) (L K : ℕ) (constant : 3≤L) (indices : n≤K)
    (capacity : 4*L+8≤K) (amountbits : (Code.ofRat amount).bits≤L)
    (cells : ∀ u v : Fin n, (Code.ofRat matrix[u.val][v.val]).bits≤L) :
    WordsWithin K (subtractCell matrix amount path u v).events := by
  have negative (q : ℚ) : (Code.ofRat (-q)).bits=(Code.ofRat q).bits := by simp [Code.ofRat,Code.bits]
  have zero : (Code.ofRat (0:ℚ)).bits=3 := by decide
  have one : 1≤K := by omega
  have ui := index_word u K indices
  have vi := index_word v K indices
  have dimension : n.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans indices
  have head := (cells u v).trans (show L≤K by omega)
  have arc := occurs_words u v path.val K indices one
  have chosen : (Code.ofRat (if (occurs u v path.val).value then amount else 0)).bits≤L := by
    split <;> first | exact amountbits | simpa only [zero] using constant
  have add : WordsWithin K (ratAdd matrix[u.val][v.val] (-(if (occurs u v path.val).value then amount else 0))).events := by
    intro event member word present
    have bound := ratAdd_words matrix[u.val][v.val] (-(if (occurs u v path.val).value then amount else 0)) event member word present
    simp only [negative] at bound
    have coefficient := cells u v
    omega
  simp only [subtractCell,Traced.bind_events,Traced.bind_value,emit_value,readRat,wordsWithin_append,
    emit,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,
    forall_eq,and_true,negative]
  exact ⟨⟨ui,dimension⟩,⟨vi,head⟩,arc,⟨one,chosen.trans (by omega)⟩,
    ⟨chosen.trans (by omega),chosen.trans (by omega)⟩,add⟩

theorem subtract_words (matrix : FlowDecomposition.FlowMatrix n) (amount : ℚ) {s t : Fin n}
    (path : G.Path s t) (L K : ℕ) (constant : 3≤L) (indices : n≤K)
    (capacity : 4*L+8≤K) (amountbits : (Code.ofRat amount).bits≤L)
    (cells : ∀ u v : Fin n, (Code.ofRat matrix[u.val][v.val]).bits≤L) :
    WordsWithin K (subtract matrix amount path).events := by
  apply Weights.materialize_words _ _ _ indices
  · intro u
    apply Weights.materialize_words _ _ _ indices
    · intro v
      exact subtractCell_words matrix amount path u v L K constant indices capacity amountbits cells
    · intro v
      exact (subtractCell_bits matrix amount path u v L constant amountbits cells).trans capacity
  · intro u
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans indices

end BuyAtBulk.Computation.Runtime.FlowUpdate
