import BuyAtBulk.Computation.Runtime.FlowExtract

set_option maxHeartbeats 1600000
namespace BuyAtBulk.Computation.Runtime.FlowExtract
open Rational
variable {n : ℕ} (input : Computation.ShortestPath.GraphEncoding n)

def wordBudget (n D F : ℕ) : ℕ := n+F+8*(2*D.size+4)+64

theorem extract_words (source target : Fin n) (D F fuel : ℕ)
    (matrix : FlowDecomposition.FlowMatrix n) (mass : ℚ) (positive : 0<D) (fuelbound : fuel≤F)
    (valid : FlowDecomposition.StateValid input.graph (Equiv.refl _) source target D matrix mass) :
    WordsWithin (wordBudget n D F) (extract input source target fuel matrix mass).events := by
  let K := wordBudget n D F
  let L := 2*D.size+4
  have constant : 3≤L := by dsimp [L]; omega
  have indices : n≤K := by dsimp [K,wordBudget]; omega
  have capacity : 4*L+8≤K := by dsimp [K,wordBudget,L]; omega
  have scalar : L≤K := by omega
  have one : 1≤K := by omega
  have three : 3≤K := by omega
  have decoded (matrix : FlowDecomposition.FlowMatrix n) :
      FlowDecomposition.decodedFlow (Equiv.refl (Fin n)) matrix=FlowDecomposition.matrixFlow matrix := by funext u v; rfl
  induction fuel generalizing matrix mass with
  | zero =>
    have massbits := FlowDecomposition.unit_bits_bound mass D positive valid.mass_den valid.mass_nonneg valid.mass_le_one
    simp only [extract,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,
      forall_eq_or_imp,forall_eq,and_true]
    repeat' apply And.intro
    all_goals omega
  | succ fuel ih =>
    have massbits : (Code.ofRat mass).bits≤L :=
      (FlowDecomposition.unit_bits_bound mass D positive valid.mass_den valid.mass_nonneg valid.mass_le_one).trans (by dsimp [L]; omega)
    have cells : ∀ u v : Fin n, (Code.ofRat matrix[u.val][v.val]).bits≤L := by
      intro u v
      have bound := FlowDecomposition.unit_bits_bound (FlowDecomposition.decodedFlow (Equiv.refl _) matrix u v) D
        positive (valid.coordinate_den u v) (valid.coordinate_nonneg u v) (valid.coordinate_le_one u v)
      exact bound.trans (by dsimp [L]; omega)
    have massK := massbits.trans scalar
    have counter : fuel.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp [K,wordBudget]; omega)
    have search := FlowSearch.positivePath_words input matrix source target K indices three (fun u v => (cells u v).trans scalar)
    have si : source.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
    have ti : target.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
    simp only [extract]
    split
    · simp only [wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
        or_false,forall_eq_or_imp,forall_eq,and_true]
      aesop
    · rename_i nonzero
      split
      · simp only [wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
          or_false,forall_eq_or_imp,forall_eq,and_true]
        aesop
      · rename_i path found
        have amount := FlowUpdate.minimum_words matrix mass path.val K indices three (massbits.trans scalar)
          (fun u v => (cells u v).trans scalar)
        have amountbits := FlowUpdate.minimum_bits matrix mass path.val L massbits cells
        have amountK := amountbits.trans scalar
        have residual := FlowUpdate.subtract_words matrix (FlowUpdate.minimum matrix mass path.val).value path L K
          constant indices capacity amountbits cells
        have negative (q : ℚ) : (Code.ofRat (-q)).bits=(Code.ofRat q).bits := by simp [Code.ofRat,Code.bits]
        have remaining : WordsWithin K (ratAdd mass (-(FlowUpdate.minimum matrix mass path.val).value)).events := by
          intro event member word present
          have bound := ratAdd_words mass (-(FlowUpdate.minimum matrix mass path.val).value) event member word present
          simp only [negative] at bound
          omega
        have source_found : FlowDecomposition.positivePath input.graph (Equiv.refl _)
            (FlowDecomposition.decodedFlow (Equiv.refl _) matrix) source target=some path := by
          simpa only [FlowSearch.positivePath_value,decoded] using found
        have updated := FlowDecomposition.state_after_subtract input.graph (Equiv.refl _) source target D matrix mass
          valid nonzero path source_found
        have tail := ih
          (FlowDecomposition.subtract input.graph (Equiv.refl _) matrix
            (FlowDecomposition.bottleneck input.graph (FlowDecomposition.decodedFlow (Equiv.refl _) matrix) mass path) path)
          (mass-FlowDecomposition.bottleneck input.graph (FlowDecomposition.decodedFlow (Equiv.refl _) matrix) mass path)
          (by omega) updated
        simp only [decoded] at tail
        have tail_actual : WordsWithin K (extract input source target fuel
            (FlowUpdate.subtract matrix (FlowUpdate.minimum matrix mass path.val).value path).value
            (mass+ -(FlowUpdate.minimum matrix mass path.val).value)).events := by
          simpa only [FlowUpdate.subtract_value,FlowUpdate.minimum_bottleneck,sub_eq_add_neg] using tail
        split <;> simp only [wordsWithin_append,emit,emit_value,ratAdd_value,negative,wordsWithin_cons,
          wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
        all_goals aesop

end BuyAtBulk.Computation.Runtime.FlowExtract
