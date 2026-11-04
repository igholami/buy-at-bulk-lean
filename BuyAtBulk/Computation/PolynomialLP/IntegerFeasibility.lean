import BuyAtBulk.Computation.PolynomialLP.BoxedWeakFeasibility
import BuyAtBulk.Computation.PolynomialLP.ExactFromSlack

/-! Actual bounded-integer feasibility decision by the proved rational
rounded ellipsoid loop. Encoding hypotheses here are discharged by the
unconditional stored-rational denominator-clearing wrapper. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP
variable {n m : ℕ}

def integerBoxDecision (input : Stored (n := n) (m := m)) (L : ℕ) : Bool :=
  match ellipsoidLoop (input.boxed.slack (feasibilitySlack n L))
      (workPrecision n (feasibilityRounds n L)) (feasibilityRounds n L) (Ellipsoid.initial n) with
  | .found _ => true
  | .exhausted _ | .degenerate _ => false

theorem integerBoxDecision_correct (input : Stored (n := n) (m := m)) (L : ℕ) (dimension : 2 ≤ n)
    (a : Fin (m + (n + n)) → Fin n → ℤ) (b : Fin (m + (n + n)) → ℤ)
    (coefficients : ∀ i j, input.boxed.coefficients[i.val][j.val] = (a i j : ℚ))
    (rhs : ∀ i, input.boxed.bounds[i.val] = (b i : ℚ))
    (a_bound : ∀ i j, (a i j).natAbs ≤ 2 ^ L) (b_bound : ∀ i, (b i).natAbs ≤ 2 ^ L) :
    integerBoxDecision input L = true ↔ ∃ x, input.boxed.problem.Feasible x := by
  constructor
  · intro accepted
    unfold integerBoxDecision at accepted
    cases computed : ellipsoidLoop (input.boxed.slack (feasibilitySlack n L))
        (workPrecision n (feasibilityRounds n L)) (feasibilityRounds n L) (Ellipsoid.initial n) with
    | exhausted state => simp only [computed, Bool.false_eq_true] at accepted
    | degenerate state => simp only [computed, Bool.false_eq_true] at accepted
    | found point =>
      have feasible := ellipsoidLoop_found (input.boxed.slack (feasibilitySlack n L)) _ _ (Ellipsoid.initial n) point computed
      have real_feasible : (input.boxed.slack (feasibilitySlack n L)).RealFeasible (realVector point) :=
        (realFeasible_cast_iff _ (fun j => point[j.val])).mpr feasible
      have expanded := slack_boxed_coordinates input (feasibilitySlack n L) (realVector point) real_feasible
      have box : ∀ j : Fin n, -feasibilitySlack n L ≤ point[j.val] ∧ point[j.val] ≤ 1 + feasibilitySlack n L := by
        intro j
        have bound := expanded j
        change -(feasibilitySlack n L : ℝ) ≤ (point[j.val] : ℝ) ∧ (point[j.val] : ℝ) ≤ 1 + (feasibilitySlack n L : ℝ) at bound
        exact_mod_cast bound
      have approximate : ∀ i : Fin (m + (n + n)), rowForm input.boxed.coefficients[i.val] (fun j => point[j.val]) ≤
          input.boxed.bounds[i.val] + feasibilitySlack n L := by
        intro i
        simpa only [Stored.problem, Stored.slack, Vector.getElem_map] using feasible i
      obtain ⟨x, exact_feasible, _⟩ := exact_of_uniform_slack input.boxed a b L coefficients rhs a_bound b_bound point box approximate
      exact ⟨x, exact_feasible⟩
  · intro feasible
    have real_coefficients : ∀ i : Fin (m + (n + n)), ∀ j : Fin n,
        |realVector input.boxed.coefficients[i.val] j| ≤ (2 : ℝ) ^ L := by
      intro i j
      have integer_abs : |a i j| ≤ ((2 ^ L : ℕ) : ℤ) := by
        have cast : ((a i j).natAbs : ℤ) ≤ ((2 ^ L : ℕ) : ℤ) := by exact_mod_cast a_bound i j
        simpa only [Int.natCast_natAbs] using cast
      have rational_abs : |input.boxed.coefficients[i.val][j.val]| ≤ (2 : ℚ) ^ L := by
        rw [coefficients i j]
        exact_mod_cast integer_abs
      change |(input.boxed.coefficients[i.val][j.val] : ℝ)| ≤ (2 : ℝ) ^ L
      exact_mod_cast rational_abs
    obtain ⟨point, computed, _⟩ := boxed_relaxed_finds input L dimension real_coefficients feasible
    simp only [integerBoxDecision, computed]

end BuyAtBulk.PolynomialLP
