import BuyAtBulk.Computation.PolynomialLP.CompactSolveRuntime
import BuyAtBulk.Computation.Runtime.PolynomialBudget

/-! Fixed, kernel-checked polynomial certificates for the actual unconditional
exact LP optimizer and the literal compact graph LP. Coefficients and degrees
are closed constants, independent of input dimensions and scalar magnitudes. -/
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
namespace BuyAtBulk.PolynomialLP.Polynomial
open Computation Computation.Runtime Computation.Rational PolynomialBudget

/- The large composed LP expressions use a syntax-first reifier. Parameter
identification does not normalize the entire budget at every recursive node;
the generated equality is still checked by the kernel. -/
open Lean Meta Elab Tactic in
private partial def reifyLP (cache : IO.Ref (Std.HashMap Lean.Expr Lean.Expr)) (k : ℕ) (symbols : Array Lean.Expr) (value : Lean.Expr) : MetaM Lean.Expr := do
  if let some result := (←cache.get)[value]? then return result
  let result ← do
    let value := value.consumeMData
    for i in [:symbols.size] do
      if value == symbols[i]! then
        let lt ← mkLt (mkNatLit i) (mkNatLit k)
        let fin := mkApp3 (mkConst ``Fin.mk) (mkNatLit k) (mkNatLit i) (←mkDecideProof lt)
        return mkApp2 (mkConst ``Term.parameter) (mkNatLit k) fin
    if let .lit (.natVal c) := value then
      return mkApp2 (mkConst ``Term.constant) (mkNatLit k) (mkNatLit c)
    let name := value.getAppFn.constName?
    let args := value.getAppArgs
    if name == some ``Nat.add || name == some ``HAdd.hAdd then
      return mkApp3 (mkConst ``Term.plus) (mkNatLit k)
        (←reifyLP cache k symbols args[args.size-2]!) (←reifyLP cache k symbols args[args.size-1]!)
    if name == some ``Nat.mul || name == some ``HMul.hMul then
      return mkApp3 (mkConst ``Term.times) (mkNatLit k)
        (←reifyLP cache k symbols args[args.size-2]!) (←reifyLP cache k symbols args[args.size-1]!)
    if name == some ``Nat.pow || name == some ``HPow.hPow || name == some ``Pow.pow then
      let exponent ← whnf args[args.size-1]!
      if let some n ← getNatValue? exponent then
        return mkApp3 (mkConst ``Term.power) (mkNatLit k)
          (←reifyLP cache k symbols args[args.size-2]!) (mkNatLit n)
      throwError "LP polynomial exponent must be fixed"
    if name == some ``Nat.succ then
      return mkApp3 (mkConst ``Term.plus) (mkNatLit k) (←reifyLP cache k symbols args[0]!)
        (mkApp2 (mkConst ``Term.constant) (mkNatLit k) (mkNatLit 1))
    if name == some ``List.sum then
      let rec listTerm (items : Lean.Expr) : MetaM Lean.Expr := do
        let items ← whnf items
        if items.isAppOf ``List.nil then
          return mkApp2 (mkConst ``Term.constant) (mkNatLit k) (mkNatLit 0)
        if items.isAppOf ``List.cons then
          let parts := items.getAppArgs
          return mkApp3 (mkConst ``Term.plus) (mkNatLit k)
            (←reifyLP cache k symbols parts[parts.size-2]!) (←listTerm parts[parts.size-1]!)
        throwError "LP polynomial list sum must have fixed finite spine"
      return ← listTerm args[args.size-1]!
    if let some unfolded ← Lean.Meta.delta? value then return ← reifyLP cache k symbols unfolded
    let reduced ← whnf value
    if reduced != value then return ← reifyLP cache k symbols reduced
    throwError "unsupported LP polynomial expression: {value}"
  cache.modify fun known => known.insert value result
  return result

elab "lp_poly_cert" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let type ← Lean.Meta.whnf (←goal.getType)
  unless type.isAppOfArity ``Certificate 3 do throwError "expected polynomial certificate"
  let args := type.getAppArgs
  let kExpr ← Lean.Meta.whnf args[0]!
  let some k ← Lean.Meta.getNatValue? kExpr | throwError "expected fixed parameter count"
  let parameters := args[1]!
  let value := args[2]!
  let mut symbols : Array Lean.Expr := #[]
  for i in [:k] do
    let lt ← Lean.Meta.mkLt (Lean.mkNatLit i) (Lean.mkNatLit k)
    let fin := Lean.mkApp3 (Lean.mkConst ``Fin.mk) (Lean.mkNatLit k) (Lean.mkNatLit i) (←Lean.Meta.mkDecideProof lt)
    symbols := symbols.push (←Lean.Meta.whnf (Lean.mkApp parameters fin))
  let cache ← IO.mkRef ({} : Std.HashMap Lean.Expr Lean.Expr)
  let term ← reifyLP cache k symbols value
  goal.assign (Lean.mkAppN (Lean.mkConst ``Certificate.mk)
    #[kExpr,parameters,value,term,←Lean.Meta.mkEqRefl value])
  Lean.Elab.Tactic.replaceMainGoal []

def parameters (n m B : ℕ) (i : Fin 3) : ℕ := if i=0 then n else if i=1 then m else B

def optimizerCount (n m B : ℕ) : Certificate (parameters n m B)
    (PolynomialLP.optimizerCount n m B) := by lp_poly_cert

def optimizerWords (n m B : ℕ) : Certificate (parameters n m B)
    (PolynomialLP.optimizerWords n m B) := by lp_poly_cert

def compactCount (n h L : ℕ) : Certificate (parameters n h L)
    (CompactEncoding.solveCount n h L) := by lp_poly_cert

def compactWords (n h L : ℕ) : Certificate (parameters n h L)
    (CompactEncoding.solveWords n h L) := by lp_poly_cert

def optimizerCountTerm : Term 3 := (optimizerCount 0 0 0).term
def optimizerWordsTerm : Term 3 := (optimizerWords 0 0 0).term
def compactCountTerm : Term 3 := (compactCount 0 0 0).term
def compactWordsTerm : Term 3 := (compactWords 0 0 0).term

@[simp] theorem optimizerCount_eval (n m B : ℕ) :
    optimizerCountTerm.eval (parameters n m B)=PolynomialLP.optimizerCount n m B :=
  (optimizerCount n m B).correct
@[simp] theorem optimizerWords_eval (n m B : ℕ) :
    optimizerWordsTerm.eval (parameters n m B)=PolynomialLP.optimizerWords n m B :=
  (optimizerWords n m B).correct
@[simp] theorem compactCount_eval (n h L : ℕ) :
    compactCountTerm.eval (parameters n h L)=CompactEncoding.solveCount n h L :=
  (compactCount n h L).correct
@[simp] theorem compactWords_eval (n h L : ℕ) :
    compactWordsTerm.eval (parameters n h L)=CompactEncoding.solveWords n h L :=
  (compactWords n h L).correct

theorem parameter_bounds {n m B S : ℕ} (vertices : n≤S) (rows : m≤S) (words : B≤S) :
    ∀ i,parameters n m B i≤S := by
  intro i
  simp only [parameters]
  split_ifs <;> assumption

theorem optimizer_runtime {n m : ℕ} (input : Stored (n:=n) (m:=m)) (S : ℕ)
    (vertices : n≤S) (rows : m≤S) (words : inputBudget input≤S) :
    (optimizeTrace input).value=optimize input ∧
      (optimizeTrace input).events.length≤optimizerCountTerm.weight*(S+1)^optimizerCountTerm.degree ∧
      WordsWithin (optimizerWordsTerm.weight*(S+1)^optimizerWordsTerm.degree) (optimizeTrace input).events := by
  have actual := optimizeTrace_runtime input
  have count := optimizerCountTerm.eval_le (parameters n m (inputBudget input)) S
    (parameter_bounds vertices rows words)
  have width := optimizerWordsTerm.eval_le (parameters n m (inputBudget input)) S
    (parameter_bounds vertices rows words)
  rw [optimizerCount_eval] at count
  rw [optimizerWords_eval] at width
  exact ⟨actual.1,actual.2.1.trans count,actual.2.2.mono width⟩

/-- Exact minimization, infeasibility reporting and bit-polynomial execution
for a single explicit stored rational input. The input length includes array
headers/dimensions and every actual normalized rational coefficient. -/
theorem exact_polynomial_optimizer {n m : ℕ} (input : Stored (n:=n) (m:=m)) :
    (optimizeTrace input).value=optimize input ∧
    (optimizeTrace input).events.length≤
      optimizerCountTerm.weight*(n+m+inputBudget input+1)^optimizerCountTerm.degree ∧
    WordsWithin (optimizerWordsTerm.weight*(n+m+inputBudget input+1)^optimizerWordsTerm.degree)
      (optimizeTrace input).events ∧
    (optimize input=none ↔ ¬∃ x,input.problem.Feasible x ∧ ∀ j,0≤x j ∧ x j≤1) ∧
    ∀ point,optimize input=some point →
      input.problem.Feasible (fun j=>point[j.val]) ∧
      (∀ j : Fin n,0≤point[j.val] ∧ point[j.val]≤1) ∧
      ∀ y,input.problem.Feasible y → (∀ j,0≤y j ∧ y j≤1) →
        input.problem.objective (fun j=>point[j.val])≤ input.problem.objective y := by
  have runtime := optimizer_runtime input (n+m+inputBudget input) (by omega) (by omega) (by omega)
  exact ⟨runtime.1,runtime.2.1,runtime.2.2,optimize_none_iff input,fun point actual=>optimize_correct input point actual⟩

/-- The source Lemma 2.3 computational contract for every explicit dense
rational input. Exact feasibility and minimization include the unit cube. -/
def ExactPolynomialOptimizerTarget : Prop :=
  ∀ (n m : ℕ) (input : Stored (n:=n) (m:=m)),
    (optimizeTrace input).value=optimize input ∧
    (optimizeTrace input).events.length≤
      optimizerCountTerm.weight*(n+m+inputBudget input+1)^optimizerCountTerm.degree ∧
    WordsWithin (optimizerWordsTerm.weight*(n+m+inputBudget input+1)^optimizerWordsTerm.degree)
      (optimizeTrace input).events ∧
    (optimize input=none ↔ ¬∃ x,input.problem.Feasible x ∧ ∀ j,0≤x j ∧ x j≤1) ∧
    ∀ point,optimize input=some point →
      input.problem.Feasible (fun j=>point[j.val]) ∧
      (∀ j : Fin n,0≤point[j.val] ∧ point[j.val]≤1) ∧
      ∀ y,input.problem.Feasible y → (∀ j,0≤y j ∧ y j≤1) →
        input.problem.objective (fun j=>point[j.val])≤ input.problem.objective y

theorem exactPolynomialOptimizer : ExactPolynomialOptimizerTarget :=
  fun _ _ input => exact_polynomial_optimizer input

theorem compact_runtime {n h : ℕ} (data : CompactEncoding.Data n h) (L S : ℕ)
    (buying : ∀ v : Fin n,(Code.ofRat data.buying[v.val]).bits≤L)
    (physical : ∀ v : Fin n,(Code.ofRat data.physical[v.val]).bits≤L)
    (demand : ∀ i : Fin h,(Code.ofRat data.demand[i.val]).bits≤L)
    (vertices : n≤S) (requests : h≤S) (words : L≤S) :
    (CompactEncoding.solveTrace data).value=CompactEncoding.solve data ∧
      (CompactEncoding.solveTrace data).events.length≤compactCountTerm.weight*(S+1)^compactCountTerm.degree ∧
      WordsWithin (compactWordsTerm.weight*(S+1)^compactWordsTerm.degree) (CompactEncoding.solveTrace data).events := by
  have actual := CompactEncoding.solveTrace_runtime data L buying physical demand
  have count := compactCountTerm.eval_le (parameters n h L) S (parameter_bounds vertices requests words)
  have width := compactWordsTerm.eval_le (parameters n h L) S (parameter_bounds vertices requests words)
  rw [compactCount_eval] at count
  rw [compactWords_eval] at width
  exact ⟨actual.1,actual.2.1.trans count,actual.2.2.mono width⟩
end BuyAtBulk.PolynomialLP.Polynomial
