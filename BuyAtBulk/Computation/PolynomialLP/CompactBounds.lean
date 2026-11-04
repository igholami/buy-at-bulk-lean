import BuyAtBulk.Computation.PolynomialLP.CompactOptimization

namespace BuyAtBulk.PolynomialLP.CompactEncoding
open CompactFlow Computation.Rational
variable {n h : ℕ}

theorem coefficient_bits (data : Data n h) (r : ConstraintIndex (Fin n) h)
    (c : VariableIndex (Fin n) h) : (Code.ofRat (coefficient data r c)).bits ≤ 4 := by
  rcases r with ⟨upper,r⟩ | ⟨i,v⟩ | ⟨⟨positive,incoming⟩,i,v⟩ | ⟨i,u,v⟩
  · cases upper <;> simp only [coefficient] <;> (try split_ifs) <;> norm_num [Code.ofRat,Code.bits]
  · rcases c with w | ⟨j,w⟩ | ⟨j,u,w⟩ <;>
      simp only [coefficient,nodeCoefficient,openingCoefficient] <;> (try split_ifs) <;> norm_num [Code.ofRat,Code.bits]
  · cases positive <;> cases incoming <;>
      rcases c with w | ⟨j,w⟩ | ⟨j,u,w⟩ <;>
      simp only [coefficient,balanceCoefficient,nodeCoefficient,Bool.false_eq_true,↓reduceIte] <;>
      (try split_ifs) <;> norm_num [Code.ofRat,Code.bits]
  · simp only [coefficient]
    (try split_ifs) <;> norm_num [Code.ofRat,Code.bits]

theorem bound_bits (data : Data n h) (r : ConstraintIndex (Fin n) h) :
    (Code.ofRat (bound data r)).bits ≤ 4 := by
  rcases r with ⟨upper,r⟩ | ⟨i,v⟩ | ⟨⟨positive,incoming⟩,i,v⟩ | ⟨i,u,v⟩
  · simp only [bound]; (try split_ifs) <;> norm_num [Code.ofRat,Code.bits]
  · norm_num [bound,Code.ofRat,Code.bits]
  · simp only [bound]; (try split_ifs) <;> norm_num [Code.ofRat,Code.bits]
  · norm_num [bound,Code.ofRat,Code.bits]

theorem objective_bits (data : Data n h) (L : ℕ) (constant : 3≤L)
    (buying : ∀ v : Fin n, (Code.ofRat data.buying[v.val]).bits≤L)
    (physical : ∀ v : Fin n, (Code.ofRat data.physical[v.val]).bits≤L)
    (demand : ∀ i : Fin h, (Code.ofRat data.demand[i.val]).bits≤L)
    (c : VariableIndex (Fin n) h) : (Code.ofRat (objective data c)).bits≤4*L+8 := by
  rcases c with v | ⟨i,v⟩ | ⟨i,u,v⟩
  · exact (buying v).trans (by omega)
  · have product := Computation.Runtime.ratMul_result_bits data.demand[i.val] data.physical[v.val]
    have d := demand i
    have p := physical v
    exact product.trans (by omega)
  · have zero : (Code.ofRat (0:ℚ)).bits=3 := by decide
    simp only [objective,zero]
    omega

end BuyAtBulk.PolynomialLP.CompactEncoding
