import BuyAtBulk.Computation.PolynomialLP.Trace.Rounded
import BuyAtBulk.Computation.PolynomialLP.Trace.Separation
import BuyAtBulk.Computation.PolynomialLP.MatrixArithmeticBits

set_option autoImplicit false
set_option maxHeartbeats 600000
namespace BuyAtBulk.PolynomialLP.Trace
open BuyAtBulk.Computation BuyAtBulk.Computation.Runtime
open Rational
variable {n m : ℕ}

def initialCell (dimension : ℚ) (i j : Fin n) : Traced ℚ := do
  let equal ← emit .natCompare [i.val.size,j.val.size] (decide (i=j))
  emit .branch [1] (if equal then dimension else 0)
@[simp] theorem initialCell_value (dimension : ℚ) (i j : Fin n) :
    (initialCell dimension i j).value = if i=j then dimension else 0 := by
  simp [initialCell]
@[simp] theorem initialCell_count (dimension : ℚ) (i j : Fin n) :
    (initialCell dimension i j).events.length = 2 := by
  simp [initialCell, Traced.bind_events, List.length_append]

def initial (n : ℕ) : Traced (Ellipsoid n) :=
  let dimension := ratCast n
  let half := ratDiv 1 2
  let center := Weights.materialize (fun _ : Fin n => Traced.pure half.value) (fun q => (Code.ofRat q).bits)
  let shape := Weights.materialize (fun i : Fin n => Weights.materialize
    (initialCell dimension.value i) (fun q => (Code.ofRat q).bits)) (fun _ => n.size)
  ⟨⟨center.value,shape.value⟩,dimension.events++half.events++center.events++shape.events++[⟨.write,[n.size]⟩]⟩

theorem initial_value (n : ℕ) : (initial n).value = Ellipsoid.initial n := by
  simp only [initial, Ellipsoid.initial, ratCast, emit_value, ratDiv_value]
  congr 1
  · apply Vector.ext
    intro i bound
    simp only [materialize_getNat, Traced.pure_value, Vector.getElem_replicate]
  · apply Vector.ext
    intro i bound
    apply Vector.ext
    intro j boundj
    simp only [materialize_getNat, initialCell_value, Vector.getElem_ofFn]

theorem initial_count (n : ℕ) : (initial n).events.length ≤ 4*n^2+5*n+6 := by
  have center := Weights.materialize_count (fun _ : Fin n => Traced.pure ((1:ℚ)/2))
    (fun q => (Code.ofRat q).bits) 0 (by intro i; rfl)
  have rows (i : Fin n) := Weights.materialize_count (initialCell (n:ℚ) i)
    (fun q => (Code.ofRat q).bits) 2 (by intro j; simp)
  have shape := Weights.materialize_count (fun i : Fin n => Weights.materialize
    (initialCell (n:ℚ) i) (fun q => (Code.ofRat q).bits)) (fun _ => n.size) (n*4+1) rows
  simp only [initial, ratCast, emit_length, emit_value, ratDiv_length, ratDiv_value,
    List.length_append, List.length_cons, List.length_nil]
  nlinarith

def step (state : Ellipsoid n) (direction : Vector ℚ n) (precision : ℕ) : Traced (Option (Ellipsoid n)) := do
  let small ← emit .natCompare [n.size, 1] (decide (n≤1))
  let small ← branch small
  if small then Traced.pure none else do
    let q ← quadratic state.shape direction
    let nonpositive ← ratLe q 0
    let nonpositive ← branch nonpositive
    if nonpositive then Traced.pure none else do
      let next ← roundedStep state direction precision
      emit .write [n.size] (some next)

theorem step_value (state : Ellipsoid n) (direction : Vector ℚ n) (precision : ℕ) :
    (step state direction precision).value = state.step direction precision := by
  simp only [step, Traced.bind_value, emit_value, branch, Ellipsoid.step]
  by_cases small : n≤1
  · simp only [small, decide_true, Bool.true_eq, if_pos, Traced.pure_value]
  · simp only [small, decide_false, Bool.false_eq_true, if_false,
      Traced.bind_value, quadratic_value, ratLe, emit_value, branch]
    by_cases nonpositive : PolynomialLP.quadratic state.shape direction ≤ 0
    · simp only [nonpositive, decide_true, Bool.true_eq, if_pos, Traced.pure_value]
    · simp only [nonpositive, decide_false, Bool.false_eq_true, if_false,
        Traced.bind_value, roundedStep_value, emit_value]

def stepBudget (n precision Q : ℕ) : ℕ :=
  roundedStepBudget n precision Q+7*n^2+16*n+6

theorem step_count (state : Ellipsoid n) (direction : Vector ℚ n) (precision : ℕ) :
    (step state direction precision).events.length ≤
      stepBudget n precision (Code.ofRat (PolynomialLP.quadratic state.shape direction)).bits := by
  have q := quadratic_count state.shape direction
  have rounded := roundedStep_count state direction precision
  simp only [step, Traced.bind_events, Traced.bind_value, emit_length, emit_value, branch]
  by_cases small : n≤1
  · simp only [small, decide_true, Bool.true_eq, if_pos, Traced.pure_events, List.length_nil, emit, List.length_append]
    dsimp [stepBudget, roundedStepBudget]
    omega
  · simp only [small, decide_false, Bool.false_eq_true, if_false, Traced.bind_events,
      Traced.bind_value, quadratic_value, ratLe, emit_length, emit_value, branch, List.length_append]
    by_cases nonpositive : PolynomialLP.quadratic state.shape direction ≤ 0
    · simp only [nonpositive, decide_true, Bool.true_eq, if_pos, Traced.pure_events, List.length_nil, emit, List.length_append]
      dsimp [stepBudget]
      omega
    · simp only [nonpositive, decide_false, Bool.false_eq_true, if_false, Traced.bind_events,
        List.length_append, emit_length]
      dsimp [stepBudget]
      omega

def loop (input : Stored (n:=n) (m:=m)) (precision : ℕ) :
    ℕ → Ellipsoid n → Traced (EllipsoidOutcome n)
  | 0, state => emit .write [n.size] (.exhausted state)
  | fuel+1, state => do
    let _ ← emit .recurse [fuel.size] ()
    let separated ← separate input state.center
    let separated ← emit .branch [1] separated
    match separated with
    | none => emit .write [n.size] (.found state.center)
    | some row => do
      let direction ← emit .read [row.val.size, n.size] input.coefficients[row.val]
      let next ← step state direction precision
      let next ← emit .branch [1] next
      match next with
      | none => emit .write [n.size] (.degenerate state)
      | some next => loop input precision fuel next

theorem loop_value (input : Stored (n:=n) (m:=m)) (precision fuel : ℕ) (state : Ellipsoid n) :
    (loop input precision fuel state).value = ellipsoidLoop input precision fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    simp only [loop, Traced.bind_value, emit_value, separate_value, ellipsoidLoop]
    cases separated : (PolynomialLP.separate input state.center).value with
    | none => rfl
    | some row =>
      simp only [Traced.bind_value, emit_value, step_value]
      cases stepped : state.step input.coefficients[row.val] precision with
      | none => rfl
      | some next => exact ih next

def loopBudget (n m precision Q fuel : ℕ) : ℕ :=
  fuel*((10*n+8)*m+stepBudget n precision Q+5)+1

/-- Uniform arithmetic event bound along every actual successful update.
The geometric invariant is available even for infeasible inputs. -/
theorem loop_count (input : Stored (n:=n) (m:=m)) (rounds fuel age S : ℕ)
    (constant : 5≤S)
    (coefficients : ∀ i : Fin m, ∀ j : Fin n, (Code.ofRat input.coefficients[i.val][j.val]).bits+1≤S)
    (encoding : 2*(n+1+4*(rounds+1)+workPrecision n rounds+1)+3≤S)
    (state : Ellipsoid n) (elapsed : age+fuel≤rounds) (valid : EllipsoidInvariant state age)
    (shapeBits : ∀ i j : Fin n, (Code.ofRat state.shape[i.val][j.val]).bits+1≤S) :
    (loop input (workPrecision n rounds) fuel state).events.length ≤
      loopBudget n m (workPrecision n rounds)
        (matrixProductBudget n (matrixProductBudget n S+S+5)) fuel := by
  induction fuel generalizing age state with
  | zero => simp [loop, emit, loopBudget]
  | succ fuel ih =>
    have sep := separate_count input state.center
    have perrow (row : Fin m) : (step state input.coefficients[row.val] (workPrecision n rounds)).events.length ≤
        stepBudget n (workPrecision n rounds) (matrixProductBudget n (matrixProductBudget n S+S+5)) := by
      have actual := step_count state input.coefficients[row.val] (workPrecision n rounds)
      have q := quadratic_bits state.shape input.coefficients[row.val] S constant shapeBits (coefficients row)
      dsimp [stepBudget, roundedStepBudget] at actual ⊢
      omega
    simp only [loop, Traced.bind_events, Traced.bind_value, emit_length, emit_value,
      separate_value, List.length_append]
    cases separated : (PolynomialLP.separate input state.center).value with
    | none =>
      simp only [emit_length]
      dsimp [loopBudget]
      nlinarith
    | some row =>
      have thisStep := perrow row
      simp only [Traced.bind_events, Traced.bind_value, emit_length, emit_value,
        step_value, List.length_append]
      cases stepped : state.step input.coefficients[row.val] (workPrecision n rounds) with
      | none =>
        simp only [emit_length]
        dsimp [loopBudget]
        nlinarith
      | some next =>
        have nextValid := step_success_invariant state next input.coefficients[row.val] rounds age
          (by omega) valid stepped
        have nextBits := (step_success_encoding state next input.coefficients[row.val] rounds age
          (by omega) valid stepped).2
        have recursive := ih (age+1) next (by omega) nextValid (by
          intro i j
          have b := nextBits i j
          omega)
        dsimp [loopBudget] at recursive ⊢
        nlinarith

end BuyAtBulk.PolynomialLP.Trace
