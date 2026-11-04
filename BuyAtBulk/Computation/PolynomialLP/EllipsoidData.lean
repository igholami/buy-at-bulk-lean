import BuyAtBulk.Computation.PolynomialLP.Separation
import BuyAtBulk.Computation.PolynomialLP.SquareRoot
import BuyAtBulk.Computation.PolynomialLP.Dyadic
import BuyAtBulk.Computation.PolynomialLP.Normalization

/-! Concrete rational rounded central-cut iteration on stored arrays.
Success is sound. Totality at a polynomial fuel schedule, matrix containment
and bounded-word invariants are NOT yet established by this draft module. -/
namespace BuyAtBulk.PolynomialLP
variable {n m : ℕ}

structure Ellipsoid (n : ℕ) where
  center : Vector ℚ n
  shape : Vector (Vector ℚ n) n

def matrixVector (shape : Vector (Vector ℚ n) n) (direction : Vector ℚ n) : Vector ℚ n :=
  Vector.ofFn fun i => ((List.finRange n).map fun j => shape[i.val][j.val] * direction[j.val]).sum

def quadratic (shape : Vector (Vector ℚ n) n) (direction : Vector ℚ n) : ℚ :=
  let image := matrixVector shape direction
  ((List.finRange n).map fun i => direction[i.val] * image[i.val]).sum

def Ellipsoid.initial (n : ℕ) : Ellipsoid n where
  center := Vector.replicate n (1 / 2)
  shape := Vector.ofFn fun i => Vector.ofFn fun j => if i = j then (n : ℚ) else 0

def Ellipsoid.rawCenter (state : Ellipsoid n) (direction : Vector ℚ n) : Vector ℚ n :=
  let image := matrixVector state.shape direction
  let upperRoot := normalizationRoot (quadratic state.shape direction) n
  Vector.ofFn fun i => state.center[i.val] - image[i.val] / (((n : ℚ) + 1) * upperRoot)

def Ellipsoid.rawShape (state : Ellipsoid n) (direction : Vector ℚ n) : Vector (Vector ℚ n) n :=
  let image := matrixVector state.shape direction
  let q := quadratic state.shape direction
  Vector.ofFn fun i => Vector.ofFn fun j =>
    ((n : ℚ) ^ 2 / ((n : ℚ) ^ 2 - 1)) *
      (state.shape[i.val][j.val] - (2 / (((n : ℚ) + 1) * q)) * image[i.val] * image[j.val])

def stepEta (n : ℕ) : ℚ := 1 / (64 * (n : ℚ) * (n + 1))
def stepInflation (n : ℕ) : ℚ := (1 + 2 * stepEta n) ^ 2

def Ellipsoid.roundedStep (state : Ellipsoid n) (direction : Vector ℚ n) (precision : ℕ) : Ellipsoid n :=
  let rawCenter := state.rawCenter direction
  let rawShape := state.rawShape direction
  let inflation := stepInflation n
  let diagonal := (n : ℚ) / (2 : ℚ) ^ precision
  { center := rawCenter.map fun q => (dyadicCode q precision).value
    shape := Vector.ofFn fun i => Vector.ofFn fun j =>
      (dyadicCode (inflation * rawShape[i.val][j.val]) precision).value +
        (if i = j then diagonal else 0) }

/-- The step executes only rational/integer arithmetic, a proved rational
sqrt bracket and dyadic rounding. Its control flow does not use real geometry. -/
def Ellipsoid.step (state : Ellipsoid n) (direction : Vector ℚ n) (precision : ℕ) : Option (Ellipsoid n) :=
  if n ≤ 1 then none else
    let q := quadratic state.shape direction
    if q ≤ 0 then none else
      some (state.roundedStep direction precision)

inductive EllipsoidOutcome (n : ℕ) where
  | found : Vector ℚ n → EllipsoidOutcome n
  | exhausted : Ellipsoid n → EllipsoidOutcome n
  | degenerate : Ellipsoid n → EllipsoidOutcome n

def ellipsoidLoop (input : Stored (n := n) (m := m)) (precision : ℕ) :
    ℕ → Ellipsoid n → EllipsoidOutcome n
  | 0, state => .exhausted state
  | fuel + 1, state =>
      match (separate input state.center).value with
      | none => .found state.center
      | some row =>
        match state.step input.coefficients[row.val] precision with
        | none => .degenerate state
        | some next => ellipsoidLoop input precision fuel next

/-- Any successful computed output satisfies every stored inequality.
This statement does not conceal a totality or convergence assumption. -/
theorem ellipsoidLoop_found (input : Stored (n := n) (m := m)) (precision fuel : ℕ)
    (state : Ellipsoid n) (point : Vector ℚ n)
    (computed : ellipsoidLoop input precision fuel state = .found point) :
    input.problem.Feasible (fun j => point[j.val]) := by
  induction fuel generalizing state with
  | zero => cases computed
  | succ fuel ih =>
    simp only [ellipsoidLoop] at computed
    cases separated : (separate input state.center).value with
    | none =>
      rw [separated] at computed
      cases computed
      have correct := separate_correct input state.center
      simpa only [separated] using correct
    | some row =>
      rw [separated] at computed
      cases stepped : state.step input.coefficients[row.val] precision with
      | none => simp only [stepped] at computed; cases computed
      | some next => exact ih next (by simpa only [stepped] using computed)

end BuyAtBulk.PolynomialLP
