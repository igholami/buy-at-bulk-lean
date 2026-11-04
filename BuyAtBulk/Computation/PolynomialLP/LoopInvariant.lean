import BuyAtBulk.Computation.PolynomialLP.StateInvariant
import BuyAtBulk.Computation.PolynomialLP.RealSeparation

/-! The actual numerical separation/update loop preserves the complete
geometric invariant. Nonempty-region hypotheses occur in this completeness
proof, not in the algorithm's data or final decision interface. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.PolynomialLP
open scoped Matrix
variable {n m : ℕ}

def RegionInside (input : Stored (n := n) (m := m)) (state : Ellipsoid n) : Prop :=
  ∀ point, input.RealFeasible point → DualBall (realMatrix state.shape) (point - realVector state.center)

def LoopConclusion (input : Stored (n := n) (m := m)) (age : ℕ) : EllipsoidOutcome n → Prop
  | .found point => input.RealFeasible (realVector point)
  | .exhausted state => EllipsoidInvariant state age ∧ RegionInside input state
  | .degenerate _ => False

theorem ellipsoidLoop_invariant (input : Stored (n := n) (m := m)) (rounds : ℕ)
    (dimension : 2 ≤ n) (nonempty : ∃ point, input.RealFeasible point) (fuel : ℕ)
    (state : Ellipsoid n) (age : ℕ) (remaining : age + fuel ≤ rounds)
    (valid : EllipsoidInvariant state age) (contains : RegionInside input state) :
    LoopConclusion input (age + fuel) (ellipsoidLoop input (workPrecision n rounds) fuel state) := by
  induction fuel generalizing state age with
  | zero => simpa only [ellipsoidLoop, LoopConclusion, Nat.add_zero] using And.intro valid contains
  | succ fuel ih =>
    cases separated : (separate input state.center).value with
    | none =>
      simp only [ellipsoidLoop, separated, LoopConclusion]
      exact separate_real_none input state.center separated
    | some row =>
      have direction_nonzero := separate_real_nonzero input state.center row separated nonempty
      have age_le : age ≤ rounds := by omega
      have computed := step_of_positive state input.coefficients[row.val] (workPrecision n rounds) valid.positive direction_nonzero dimension
      have next_valid := roundedStep_invariant state input.coefficients[row.val] rounds age dimension age_le valid direction_nonzero
      have next_contains : RegionInside input (state.roundedStep input.coefficients[row.val] (workPrecision n rounds)) := by
        intro point feasible
        apply roundedStep_contains state input.coefficients[row.val] (workPrecision n rounds) valid.positive direction_nonzero dimension
          ((1 / 4 : ℝ) ^ age) (fun x => (valid.forms x).1) (center_precision n rounds age dimension age_le) point
        · exact contains point feasible
        · exact separate_real_cut input state.center row separated point feasible
      have result := ih _ (age + 1) (by omega) next_valid next_contains
      have age_eq : (age + 1) + fuel = age + (fuel + 1) := by omega
      simpa only [ellipsoidLoop, separated, computed, age_eq] using result

end BuyAtBulk.PolynomialLP
