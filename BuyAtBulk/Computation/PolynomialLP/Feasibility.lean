import BuyAtBulk.Computation.PolynomialLP.IntegerFeasibility
import BuyAtBulk.Computation.PolynomialLP.IntegerData
import BuyAtBulk.Computation.PolynomialLP.LowDimension

/-! Unconditional stored-rational box-feasibility decision. The actual code
handles dimensions0/1 exactly and otherwise clears denominators, appends the
unit box and runs the proved rational rounded ellipsoid schedule. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP

def decideBoxed : {n m : ℕ} → Stored (n := n) (m := m) → Bool
  | 0, _, input => (zeroSolve input).isSome
  | 1, _, input => (unarySolve input.boxed).isSome
  | _ + 2, _, input => integerBoxDecision (integerize input) (integerL input)

/-- No solver witness, encoding certificate, nonemptiness promise or runtime
field is supplied: all integer data and precision bounds are computed. -/
theorem decideBoxed_correct {n m : ℕ} (input : Stored (n := n) (m := m)) :
    decideBoxed input = true ↔ ∃ x, input.problem.Feasible x ∧ ∀ j, 0 ≤ x j ∧ x j ≤ 1 := by
  cases n with
  | zero =>
    have correct := zeroSolve_correct input
    cases computed : zeroSolve input with
    | none =>
      simp only [computed] at correct
      simp only [decideBoxed, computed, Option.isSome_none, Bool.false_eq_true, false_iff]
      rintro ⟨x, feasible, _⟩
      exact correct ⟨x, feasible⟩
    | some point =>
      simp only [computed] at correct
      simp only [decideBoxed, computed, Option.isSome_some, true_iff]
      exact ⟨fun j => point[j.val], correct.1, fun j => j.elim0⟩
  | succ n => cases n with
    | zero =>
      cases computed : unarySolve input.boxed with
      | none =>
        have impossible := unarySolve_none input.boxed input.boxed_in_cube computed
        simp only [decideBoxed, computed, Option.isSome_none, Bool.false_eq_true, false_iff]
        rintro ⟨x, feasible, box⟩
        exact impossible ⟨x, (input.boxed_feasible x).mpr ⟨feasible, box⟩⟩
      | some point =>
        have exact_feasible := (unarySolve_some input.boxed point computed).1
        simp only [decideBoxed, computed, Option.isSome_some, true_iff]
        exact ⟨fun _ => point, (input.boxed_feasible _).mp exact_feasible⟩
    | succ n =>
      obtain ⟨coefficients, rhs, a_bound, b_bound⟩ := boxed_integer_data input
      have correct := integerBoxDecision_correct (integerize input) (integerL input) (by omega)
        (fun i j => ((integerize input).boxed.coefficients[i.val][j.val]).num)
        (fun i => ((integerize input).boxed.bounds[i.val]).num)
        coefficients rhs a_bound b_bound
      change integerBoxDecision (integerize input) (integerL input) = true ↔ _
      rw [correct]
      apply exists_congr
      intro x
      rw [Stored.boxed_feasible, integerize_feasible]

theorem decide_correct_in_cube {n m : ℕ} (input : Stored (n := n) (m := m))
    (cube : input.problem.InUnitCube) : decideBoxed input = true ↔ ∃ x, input.problem.Feasible x := by
  rw [decideBoxed_correct]
  exact ⟨fun ⟨x, feasible, _⟩ => ⟨x, feasible⟩, fun ⟨x, feasible⟩ => ⟨x, feasible, cube x feasible⟩⟩

end BuyAtBulk.PolynomialLP
