import BuyAtBulk.Computation.PolynomialLP.Trace.Loop
import BuyAtBulk.Computation.PolynomialLP.Trace.LowDimension
import BuyAtBulk.Computation.PolynomialLP.PreparationTrace
import BuyAtBulk.Computation.PolynomialLP.Feasibility

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP.Trace
open BuyAtBulk.Computation BuyAtBulk.Computation.Runtime
open Rational
variable {n m : ℕ}

def highDecision (input : Stored (n:=n) (m:=m)) : Traced Bool :=
  let prepared := InputTrace.prepareTrace input
  let state := initial n
  let result := loop prepared.value.input prepared.value.schedule.precision
    prepared.value.schedule.rounds state.value
  let accepted := match result.value with | .found _ => true | _ => false
  ⟨accepted,prepared.events++state.events++result.events++[⟨.branch,[1]⟩,⟨.write,[1]⟩]⟩

theorem highDecision_value (input : Stored (n:=n) (m:=m)) :
    (highDecision input).value = integerBoxDecision (integerize input) (integerL input) := by
  simp only [highDecision,InputTrace.prepareTrace_value,initial_value,loop_value,integerBoxDecision]
  cases ellipsoidLoop ((integerize input).boxed.slack (feasibilitySlack n (integerL input)))
    (workPrecision n (feasibilityRounds n (integerL input))) (feasibilityRounds n (integerL input))
    (Ellipsoid.initial n) <;> rfl

def decideBoxed : {n m : ℕ} → Stored (n:=n) (m:=m) → Traced Bool
  | 0, _, input =>
    let result := zeroSolve input
    ⟨result.value.isSome,[⟨.branch,[1]⟩]++result.events++[⟨.branch,[1]⟩,⟨.write,[1]⟩]⟩
  | 1, _, input =>
    let boxed := InputTrace.boxedTrace input
    let result := unarySolve boxed.value
    ⟨result.value.isSome,[⟨.branch,[1]⟩]++boxed.events++result.events++[⟨.branch,[1]⟩,⟨.write,[1]⟩]⟩
  | _+2, _, input =>
    let result := highDecision input
    ⟨result.value,[⟨.branch,[1]⟩]++result.events⟩

theorem decideBoxed_value (input : Stored (n:=n) (m:=m)) :
    (decideBoxed input).value = PolynomialLP.decideBoxed input := by
  cases n with
  | zero => simp only [decideBoxed,PolynomialLP.decideBoxed,zeroSolve_value]
  | succ n => cases n with
    | zero => simp only [decideBoxed,PolynomialLP.decideBoxed,InputTrace.boxedTrace_value,unarySolve_value]
    | succ n => exact highDecision_value input

/-- Uniform normalized matrix width for the complete finite ellipsoid run. -/
def stateWidth (n L : ℕ) : ℕ :=
  2*(n+1+4*(feasibilityRounds n L+1)+workPrecision n (feasibilityRounds n L)+1)+L+20

theorem highLoop_count (input : Stored (n:=n) (m:=m)) (dimension : 2≤n) :
    (loop ((integerize input).boxed.slack (feasibilitySlack n (integerL input)))
      (workPrecision n (feasibilityRounds n (integerL input)))
      (feasibilityRounds n (integerL input)) (Ellipsoid.initial n)).events.length ≤
      loopBudget n (m+(n+n)) (workPrecision n (feasibilityRounds n (integerL input)))
        (matrixProductBudget n (matrixProductBudget n (stateWidth n (integerL input))+
          stateWidth n (integerL input)+5)) (feasibilityRounds n (integerL input)) := by
  apply loop_count _ _ _ 0 (stateWidth n (integerL input))
  · dsimp [stateWidth];omega
  · intro i j
    have bound := (InputTrace.integerized_boxed_bits input).1 i j
    simp only [Stored.slack,Vector.getElem_map]
    dsimp [stateWidth];omega
  · dsimp [stateWidth];omega
  · omega
  · exact initial_invariant n dimension
  · intro i j
    simp only [Ellipsoid.initial,Vector.getElem_ofFn]
    split
    · have bits : (Code.ofRat (n:ℚ)).bits = n.size+3 := by simp [Code.ofRat,Code.bits]
      have size : n.size≤n := Nat.size_le.mpr Nat.lt_two_pow_self
      dsimp [stateWidth]
      omega
    · have bits : (Code.ofRat (0:ℚ)).bits = 3 := by decide
      dsimp [stateWidth]
      omega

def decisionCount (n m B : ℕ) : ℕ :=
  let L := (n+2)*B
  let S := stateWidth n L
  InputTrace.preparationCount n m B + (4*n^2+5*n+6) +
    loopBudget n (m+(n+n)) (workPrecision n (feasibilityRounds n L))
      (matrixProductBudget n (matrixProductBudget n S+S+5)) (feasibilityRounds n L)+
    (10*n*n+42*n+6*m+10)+16*(m+2)+8*m+20

theorem highDecision_count (input : Stored (n:=n) (m:=m)) (dimension : 2≤n) :
    (highDecision input).events.length+1 ≤ decisionCount n m (inputBudget input) := by
  have preparation := InputTrace.prepareTrace_count input
  have start := initial_count n
  have iteration := highLoop_count input dimension
  simp only [highDecision,List.length_append,InputTrace.prepareTrace_value,initial_value,
    List.length_cons,List.length_nil]
  dsimp only [decisionCount]
  simp only [integerL] at iteration ⊢
  omega

theorem decideBoxed_count (input : Stored (n:=n) (m:=m)) :
    (decideBoxed input).events.length ≤ decisionCount n m (inputBudget input) := by
  cases n with
  | zero =>
    have count := zeroSolve_count input
    simp only [decideBoxed,List.length_append,List.length_cons,List.length_nil]
    dsimp only [decisionCount]
    omega
  | succ n => cases n with
    | zero =>
      have box := InputTrace.boxedTrace_count input
      have solve := unarySolve_count input.boxed
      simp only [decideBoxed,List.length_append,List.length_cons,List.length_nil,InputTrace.boxedTrace_value]
      dsimp only [decisionCount]
      omega
    | succ n =>
      have count := highDecision_count input (by omega)
      simpa only [decideBoxed,List.length_append,List.length_cons,List.length_nil,Nat.add_zero,Nat.add_comm] using count

end BuyAtBulk.PolynomialLP.Trace
