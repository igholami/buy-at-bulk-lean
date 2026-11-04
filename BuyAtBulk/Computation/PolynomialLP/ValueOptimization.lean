import BuyAtBulk.Computation.PolynomialLP.Feasibility
import BuyAtBulk.Computation.PolynomialLP.SearchPrecision
import BuyAtBulk.Computation.PolynomialLP.CutData

/-! Actual exact objective-value optimization using the unconditional rational
feasibility Boolean. Vertex encoding is an analysis invariant; the program
never reads a feasible/optimal point supplied by a witness. -/
namespace BuyAtBulk.PolynomialLP
open RationalLP Computation.Rational
variable {n m : ℕ}

def objectiveBits (input : Stored (n := n) (m := m)) : ℕ :=
  ((List.finRange n).map fun j => (Code.ofRat input.objective[j.val]).bits).sum

theorem objectiveBits_bound (input : Stored (n := n) (m := m)) (j : Fin n) :
    (Code.ofRat (input.problem.objective (Pi.single j 1))).bits ≤ objectiveBits input := by
  have value : input.problem.objective (Pi.single j 1) = input.objective[j.val] := by
    simp [Stored.problem,rowForm_apply,Pi.single_apply,mul_ite]
  rw [value]
  exact List.single_le_sum (fun x _ => Nat.zero_le x) _ (List.mem_map.mpr ⟨j,List.mem_finRange j,rfl⟩)

def valueBits (input : Stored (n := n) (m := m)) (coordinateBits : ℕ) : ℕ :=
  2*(4*n+1)*(objectiveBits input+coordinateBits+5)+2

def recoverValue (input : Stored (n := n) (m := m)) (coordinateBits : ℕ) : Option ℚ :=
  let L := objectiveBits input
  let B := valueBits input coordinateBits
  recoverObjective (below (@decideBoxed n) input) (searchBracket n L)
    (searchRounds n L B) (2^(B+1))

/-- Exact functional correctness. The only hypotheses concern the feasible
set and its vertex encoding; no solver or running-time certificate is supplied. -/
theorem recoverValue_correct (input : Stored (n := n) (m := m)) (K : ℕ)
    (cube : input.problem.InUnitCube) (nonempty : ∃ x, input.problem.Feasible x)
    (vertex_words : ∀ x, input.problem.Feasible x → input.problem.Vertex x →
      ∀ j, (Code.ofRat (x j)).bits ≤ K) :
    ∃ value, recoverValue input K = some value ∧
      ∃ x, input.problem.Feasible x ∧ input.problem.Vertex x ∧ input.problem.objective x = value ∧
        ∀ y, input.problem.Feasible y → value ≤ input.problem.objective y := by
  obtain ⟨optimum,feasible,minimal⟩ := input.problem.minimum_attained cube nonempty
  obtain ⟨vertex,vertex_feasible,determined,no_larger⟩ := input.problem.vertex_domination cube optimum feasible
  have minimal_vertex : ∀ y, input.problem.Feasible y → input.problem.objective vertex ≤ input.problem.objective y :=
    fun y hy => no_larger.trans (minimal y hy)
  have encoded : (Code.ofRat (input.problem.objective vertex)).bits ≤ valueBits input K := by
    simpa only [valueBits,Fintype.card_fin] using
      linearForm_bits input.problem.objective vertex (objectiveBits input) K
        (objectiveBits_bound input) (vertex_words vertex vertex_feasible determined)
  have comparison : ∀ threshold, below (@decideBoxed n) input threshold = true ↔
      input.problem.objective vertex ≤ threshold :=
    below_boxed_correct (@decideBoxed n) (fun input => decideBoxed_correct input) input cube
      vertex vertex_feasible minimal_vertex
  have bounded := objective_bracket input.problem.objective vertex (objectiveBits input)
    (objectiveBits_bound input) (cube vertex vertex_feasible)
  simp only [Fintype.card_fin] at bounded
  have denom := denominator_le_of_bits (input.problem.objective vertex) (valueBits input K) encoded
  have returned := recoverObjective_correct (below (@decideBoxed n) input)
    (input.problem.objective vertex) comparison (searchBracket n (objectiveBits input))
    (searchRounds n (objectiveBits input) (valueBits input K)) (2^(valueBits input K+1))
    bounded.1 bounded.2 denom (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using (search_precision n (objectiveBits input) (valueBits input K)))
  exact ⟨input.problem.objective vertex,returned,vertex,vertex_feasible,determined,rfl,minimal_vertex⟩

end BuyAtBulk.PolynomialLP
