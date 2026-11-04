import BuyAtBulk.Computation.Runtime.FlowUpdateWords

namespace BuyAtBulk.Computation.Runtime.FlowExtract
open Rational
variable {n : ℕ} (input : Computation.ShortestPath.GraphEncoding n)

def extract (source target : Fin n) : ℕ → FlowDecomposition.FlowMatrix n → ℚ →
    Traced (Option (FlowDecomposition.WeightedPaths input.graph source target))
  | 0, _, mass =>
      ⟨if mass=0 then some [] else none,
        [⟨.ratCompare,[(Code.ofRat mass).bits,3]⟩,⟨.branch,[1]⟩,⟨.write,[1]⟩]⟩
  | fuel+1, matrix, mass =>
      let start : List Event := [⟨.recurse,[fuel.size]⟩,⟨.ratCompare,[(Code.ofRat mass).bits,3]⟩,⟨.branch,[1]⟩]
      if mass=0 then ⟨some [],start++[⟨.write,[1]⟩]⟩ else
        let search := FlowSearch.positivePath input matrix source target
        match search.value with
        | none => ⟨none,start++search.events++[⟨.branch,[1]⟩,⟨.write,[1]⟩]⟩
        | some path =>
            let amount := FlowUpdate.minimum matrix mass path.val
            let residual := FlowUpdate.subtract matrix amount.value path
            let negative := emit .ratNeg [(Code.ofRat amount.value).bits,(Code.ofRat (-amount.value)).bits] (-amount.value)
            let remaining := ratAdd mass negative.value
            let rest := extract source target fuel residual.value remaining.value
            let events := start++search.events++[⟨.branch,[1]⟩]++amount.events++residual.events++
              negative.events++remaining.events++rest.events++[⟨.branch,[1]⟩]
            match rest.value with
            | none => ⟨none,events++[⟨.write,[1]⟩]⟩
            | some entries => ⟨some ((amount.value,path)::entries),events++
                [⟨.write,[(Code.ofRat amount.value).bits,source.val.size,target.val.size]⟩,
                 ⟨.cons,[1]⟩,⟨.write,[1]⟩]⟩

@[simp] theorem extract_value (source target : Fin n) (fuel : ℕ)
    (matrix : FlowDecomposition.FlowMatrix n) (mass : ℚ) :
    (extract input source target fuel matrix mass).value=
      FlowDecomposition.extract input.graph (Equiv.refl _) source target fuel matrix mass := by
  have decoded (matrix : FlowDecomposition.FlowMatrix n) : FlowDecomposition.decodedFlow (Equiv.refl (Fin n)) matrix=FlowDecomposition.matrixFlow matrix := by funext u v; rfl
  induction fuel generalizing matrix mass with
  | zero => rfl
  | succ fuel ih =>
    simp only [extract,FlowDecomposition.extract,decoded]
    split
    · rfl
    · simp only [FlowSearch.positivePath_value]
      cases found : FlowDecomposition.positivePath input.graph (Equiv.refl _)
          (FlowDecomposition.matrixFlow matrix) source target with
      | none => simp [found,FlowDecomposition.decodedFlow]
      | some path =>
        simp only [found,FlowUpdate.minimum_bottleneck,FlowUpdate.subtract_value,emit_value,ratAdd_value,ih]
        cases recursive : FlowDecomposition.extract input.graph (Equiv.refl _) source target fuel
          (FlowDecomposition.subtract input.graph (Equiv.refl _) matrix
            (FlowDecomposition.bottleneck input.graph (FlowDecomposition.matrixFlow matrix) mass path) path)
          (mass+ -FlowDecomposition.bottleneck input.graph (FlowDecomposition.matrixFlow matrix) mass path) <;>
          simp_all [sub_eq_add_neg]

def stepBudget (n : ℕ) : ℕ := FlowSearch.searchBudget n+(4*n+9)*n^2+9*n+20

theorem extract_count (source target : Fin n) (fuel : ℕ)
    (matrix : FlowDecomposition.FlowMatrix n) (mass : ℚ) :
    (extract input source target fuel matrix mass).events.length≤fuel*stepBudget n+4 := by
  induction fuel generalizing matrix mass with
  | zero => simp [extract]
  | succ fuel ih =>
    have search := FlowSearch.positivePath_count input matrix source target
    have budget : FlowSearch.searchBudget n+5≤stepBudget n+4 := by dsimp [stepBudget]; omega
    simp only [extract]
    split
    · simp only [List.length_append,List.length_cons,List.length_nil,Nat.add_mul,Nat.one_mul]
      omega
    · split
      · simp only [List.length_append,List.length_cons,List.length_nil,Nat.add_mul,Nat.one_mul]
        omega
      · rename_i path found
        have length : path.val.length≤n := by simpa using path.property.length_lt.le
        have amount := FlowUpdate.minimum_count matrix mass path.val
        have residual := FlowUpdate.subtract_count matrix (FlowUpdate.minimum matrix mass path.val).value path
        have rest := ih (FlowUpdate.subtract matrix (FlowUpdate.minimum matrix mass path.val).value path).value
          (mass+ -(FlowUpdate.minimum matrix mass path.val).value)
        have cost : FlowSearch.searchBudget n+(4*path.val.length+9)*n^2+6*path.val.length+15+3*n≤stepBudget n := by
          dsimp [stepBudget]
          nlinarith [Nat.mul_le_mul_right (n^2) (show 4*path.val.length+9≤4*n+9 by omega)]
        split <;> simp only [List.length_append,List.length_cons,List.length_nil,emit_length,
          ratAdd_length,ratAdd_value,emit_value,Nat.add_mul,Nat.one_mul] <;> omega

end BuyAtBulk.Computation.Runtime.FlowExtract
