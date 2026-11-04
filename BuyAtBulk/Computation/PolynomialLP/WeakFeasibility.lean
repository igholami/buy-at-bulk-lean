import BuyAtBulk.Computation.PolynomialLP.LoopInvariant
import BuyAtBulk.Computation.PolynomialLP.Stopping

/-! Polynomial-fuel completeness of the actual rational rounded ellipsoid
loop for a region with proved inverse-exponential interior thickness. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.PolynomialLP
variable {n m : ℕ}

/-- A promised interior cube is a hypothesis of this geometric completeness
lemma only. The boxed-slack construction derives it from original feasibility
and input encoding bounds for the unconditional decision algorithm. -/
theorem ellipsoidLoop_finds (input : Stored (n := n) (m := m)) (radiusBits : ℕ)
    (dimension : 2 ≤ n) (initial_contains : RegionInside input (Ellipsoid.initial n))
    (base : Fin n → ℝ) (radius : ℝ) (radius_lower : 1 / (2 : ℝ) ^ radiusBits ≤ radius)
    (interior : ∀ point, (∀ i, |point i - base i| ≤ radius) → input.RealFeasible point) :
    ∃ point : Vector ℚ n,
      ellipsoidLoop input (workPrecision n (stoppingRounds n radiusBits)) (stoppingRounds n radiusBits)
        (Ellipsoid.initial n) = .found point ∧ input.RealFeasible (realVector point) := by
  let T := stoppingRounds n radiusBits
  have radius_nonneg : 0 ≤ radius := (by positivity : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ radiusBits).trans radius_lower
  have nonempty : ∃ point, input.RealFeasible point := ⟨base, interior base (by intro i; simpa only [sub_self, abs_zero] using radius_nonneg)⟩
  have invariant := ellipsoidLoop_invariant input T dimension nonempty T (Ellipsoid.initial n) 0
    (by simp) (initial_invariant n dimension) initial_contains
  cases computed : ellipsoidLoop input (workPrecision n T) T (Ellipsoid.initial n) with
  | found point =>
    refine ⟨point, rfl, ?_⟩
    simpa only [computed, LoopConclusion] using invariant
  | degenerate state => simp only [computed, LoopConclusion] at invariant
  | exhausted state =>
    simp only [computed, LoopConclusion, Nat.zero_add] at invariant
    obtain ⟨valid, contains⟩ := invariant
    have cube : CubeInside (realMatrix state.shape) (realVector state.center) base radius := by
      intro point near
      exact contains point (interior point near)
    have lower := cube_determinant_lower (realMatrix state.shape) valid.positive.isHermitian
      (realVector state.center) base radius radius_nonneg cube
    have upper := valid.determinant
    have stopping := stopping_determinant_bound n radiusBits
    have radius_power : (1 / (2 : ℝ) ^ radiusBits) ^ (2 * n) ≤ radius ^ (2 * n) := by
      gcongr
    have strict : (realMatrix state.shape).det < radius ^ (2 * n) :=
      upper.trans_lt (stopping.trans_le radius_power)
    exact (not_lt_of_ge lower strict).elim

end BuyAtBulk.PolynomialLP
