import BuyAtBulk.Computation.PolynomialLP.RationalReconstruction

/-! Exact objective recovery composed with a feasibility decision procedure.
This generic composition is not a supplied solver: its decision-correctness
hypothesis must be discharged by the actual proved feasibility algorithm. -/
namespace BuyAtBulk.PolynomialLP

structure Bracket where
  lower : ℚ
  upper : ℚ

def bisect (decideBelow : ℚ → Bool) : ℕ → Bracket → Bracket
  | 0, bracket => bracket
  | rounds+1, bracket =>
      let midpoint := (bracket.lower+bracket.upper)/2
      if decideBelow midpoint then bisect decideBelow rounds ⟨bracket.lower,midpoint⟩
      else bisect decideBelow rounds ⟨midpoint,bracket.upper⟩

theorem bisect_contains (decideBelow : ℚ → Bool) (optimum : ℚ)
    (decision : ∀ q, decideBelow q = true ↔ optimum ≤ q) (rounds : ℕ) (bracket : Bracket)
    (lower : bracket.lower ≤ optimum) (upper : optimum ≤ bracket.upper) :
    (bisect decideBelow rounds bracket).lower ≤ optimum ∧
      optimum ≤ (bisect decideBelow rounds bracket).upper := by
  induction rounds generalizing bracket with
  | zero => exact ⟨lower,upper⟩
  | succ rounds ih =>
    simp only [bisect]
    split
    · rename_i yes
      exact ih _ lower ((decision _).mp yes)
    · rename_i no
      have below : (bracket.lower+bracket.upper)/2 < optimum := by
        by_contra fail
        exact no ((decision _).mpr (le_of_not_gt fail))
      exact ih _ below.le upper

theorem bisect_width (decideBelow : ℚ → Bool) (rounds : ℕ) (bracket : Bracket) :
    (bisect decideBelow rounds bracket).upper-(bisect decideBelow rounds bracket).lower =
      (bracket.upper-bracket.lower)/(2 : ℚ)^rounds := by
  induction rounds generalizing bracket with
  | zero => simp [bisect]
  | succ rounds ih =>
    simp only [bisect]
    split <;> rw [ih] <;> dsimp only
    all_goals rw [pow_succ]; field_simp; ring

def recoverObjective (decideBelow : ℚ → Bool) (bracket : Bracket) (rounds D : ℕ) : Option ℚ :=
  let result := bisect decideBelow rounds bracket
  reconstruct result.lower result.upper D

/-- If the actual decision procedure is exact, bisection and the computed
continued fractions return the exact optimum, not an approximation or a
noncomputably selected rational number. -/
theorem recoverObjective_correct (decideBelow : ℚ → Bool) (optimum : ℚ)
    (decision : ∀ q, decideBelow q = true ↔ optimum ≤ q) (bracket : Bracket) (rounds D : ℕ)
    (lower : bracket.lower ≤ optimum) (upper : optimum ≤ bracket.upper)
    (denominator : optimum.den ≤ D)
    (precision : (bracket.upper-bracket.lower)/(2 : ℚ)^rounds < 1/(2*(D : ℚ)^2)) :
    recoverObjective decideBelow bracket rounds D = some optimum := by
  have contains := bisect_contains decideBelow optimum decision rounds bracket lower upper
  apply reconstruct_correct _ _ optimum D contains.1 contains.2 denominator
  simpa only [bisect_width] using precision

end BuyAtBulk.PolynomialLP
