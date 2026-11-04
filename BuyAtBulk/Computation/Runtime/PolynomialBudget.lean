import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Lean

/-! Checkable fixed polynomial budgets. Syntax contains only nonnegative
constants, finitely many input parameters, addition, multiplication and fixed
natural powers. The bound is computed from that syntax, not supplied as an
unverified asymptotic estimate. -/
namespace BuyAtBulk.Computation.Runtime.PolynomialBudget

inductive Term (k : ℕ) where
  | constant : ℕ → Term k
  | parameter : Fin k → Term k
  | plus : Term k → Term k → Term k
  | times : Term k → Term k → Term k
  | power : Term k → ℕ → Term k
  deriving Repr

namespace Term
variable {k j : ℕ}

def eval (parameters : Fin k → ℕ) : Term k → ℕ
  | .constant c => c
  | .parameter i => parameters i
  | .plus a b => eval parameters a+eval parameters b
  | .times a b => eval parameters a*eval parameters b
  | .power a n => eval parameters a^n

def degree : Term k → ℕ
  | .constant _ => 0
  | .parameter _ => 1
  | .plus a b => max a.degree b.degree
  | .times a b => a.degree+b.degree
  | .power a n => a.degree*n

def weight : Term k → ℕ
  | .constant c => c
  | .parameter _ => 1
  | .plus a b => a.weight+b.weight
  | .times a b => a.weight*b.weight
  | .power a n => a.weight^n


theorem eval_le (term : Term k) (parameters : Fin k → ℕ) (S : ℕ) (bounds : ∀ i,parameters i≤S) :
    term.eval parameters≤term.weight*(S+1)^term.degree := by
  induction term with
  | constant c => simp[eval,weight,degree]
  | parameter i => simpa[eval,weight,degree] using (bounds i).trans (Nat.le_succ S)
  | plus a b ha hb =>
    have first := Nat.mul_le_mul_left a.weight (Nat.pow_le_pow_right (by omega : 1≤S+1) (Nat.le_max_left a.degree b.degree))
    have second := Nat.mul_le_mul_left b.weight (Nat.pow_le_pow_right (by omega : 1≤S+1) (Nat.le_max_right a.degree b.degree))
    simp only[eval,weight,degree]
    nlinarith
  | times a b ha hb =>
    calc
      _ ≤ (a.weight*(S+1)^a.degree)*(b.weight*(S+1)^b.degree) := Nat.mul_le_mul ha hb
      _ = _ := by simp only[weight,degree,pow_add];ring
  | power a n ha =>
    calc
      _ ≤ (a.weight*(S+1)^a.degree)^n := Nat.pow_le_pow_left ha n
      _ = _ := by simp only[weight,degree,mul_pow,pow_mul]


theorem eval_mono (term : Term k) (parameters upper : Fin k → ℕ) (bounds : ∀ i,parameters i≤upper i) :
    term.eval parameters≤term.eval upper := by
  induction term with
  | constant c => rfl
  | parameter i => exact bounds i
  | plus a b ha hb => exact Nat.add_le_add ha hb
  | times a b ha hb => exact Nat.mul_le_mul ha hb
  | power a n ha => exact Nat.pow_le_pow_left ha n


def substitute (replacement : Fin k → Term j) : Term k → Term j
  | .constant c => .constant c
  | .parameter i => replacement i
  | .plus a b => .plus (a.substitute replacement) (b.substitute replacement)
  | .times a b => .times (a.substitute replacement) (b.substitute replacement)
  | .power a n => .power (a.substitute replacement) n

@[simp] theorem eval_substitute (term : Term k) (replacement : Fin k → Term j) (parameters : Fin j → ℕ) :
    (term.substitute replacement).eval parameters=term.eval (fun i => (replacement i).eval parameters) := by
  induction term <;>simp_all[substitute,eval]

end Term

structure Certificate {k : ℕ} (parameters : Fin k → ℕ) (value : ℕ) where
  term : Term k
  correct : term.eval parameters=value

namespace Certificate
variable {k : ℕ} {parameters : Fin k → ℕ} {value : ℕ}

theorem bound (certificate : Certificate parameters value) (S : ℕ) (bounds : ∀ i,parameters i≤S) :
    value≤certificate.term.weight*(S+1)^certificate.term.degree := by
  exact certificate.correct.symm.trans_le (certificate.term.eval_le parameters S bounds)


theorem monotone (certificate : Certificate parameters value) (upper : Fin k → ℕ) (bounds : ∀ i,parameters i≤upper i) :
    value≤certificate.term.eval upper := by
  exact certificate.correct.symm.trans_le (certificate.term.eval_mono parameters upper bounds)

end Certificate

open Lean Meta Elab Tactic in
private partial def reify (k : ℕ) (symbols : Array Lean.Expr) (value : Lean.Expr) : MetaM Lean.Expr := do
  for i in [:symbols.size] do
    if ← isDefEq value symbols[i]! then
      let finType := mkApp (mkConst ``Fin) (mkNatLit k)
      let lt ← mkLt (mkNatLit i) (mkNatLit k)
      let fin := mkApp3 (mkConst ``Fin.mk) (mkNatLit k) (mkNatLit i) (←mkDecideProof lt)
      unless ← isDefEq (←inferType fin) finType do throwError "invalid polynomial parameter"
      return mkApp2 (mkConst ``Term.parameter) (mkNatLit k) fin
  if let some c ← getNatValue? value then
    return mkApp2 (mkConst ``Term.constant) (mkNatLit k) (mkNatLit c)
  let name := value.getAppFn.constName?
  let args := value.getAppArgs
  if name == some ``Nat.add || name == some ``HAdd.hAdd then
    let first := args[args.size-2]!
    let second := args[args.size-1]!
    return mkApp3 (mkConst ``Term.plus) (mkNatLit k) (←reify k symbols first) (←reify k symbols second)
  if name == some ``Nat.mul || name == some ``HMul.hMul then
    return mkApp3 (mkConst ``Term.times) (mkNatLit k) (←reify k symbols args[args.size-2]!) (←reify k symbols args[args.size-1]!)
  if name == some ``Nat.pow || name == some ``HPow.hPow || name == some ``Pow.pow then
    let exponent ← whnf args[args.size-1]!
    if let some n ← getNatValue? exponent then
      return mkApp3 (mkConst ``Term.power) (mkNatLit k) (←reify k symbols args[args.size-2]!) (mkNatLit n)
    throwError "polynomial budgets require a fixed natural exponent"
  if name == some ``Nat.succ then
    return mkApp3 (mkConst ``Term.plus) (mkNatLit k) (←reify k symbols args[0]!)
      (mkApp2 (mkConst ``Term.constant) (mkNatLit k) (mkNatLit 1))
  if let some unfolded ← unfoldDefinition? value then
    return ← reify k symbols unfolded
  let reduced ← whnf value
  if reduced != value then return ← reify k symbols reduced
  throwError "unsupported polynomial budget expression: {value}"

/-- Reifies a fixed semiring expression into a kernel-checked certificate.
Definitions/lets are unfolded by reduction. Variable powers are rejected. -/
elab "poly_cert" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let type ← Lean.Meta.whnf (←goal.getType)
  unless type.isAppOfArity ``Certificate 3 do
    throwError "poly_cert expects a PolynomialBudget.Certificate goal"
  let args := type.getAppArgs
  let kExpr ← Lean.Meta.whnf args[0]!
  let some k ← Lean.Meta.getNatValue? kExpr | throwError "the polynomial parameter count must be a literal"
  let parameters := args[1]!
  let value := args[2]!
  let mut symbols : Array Lean.Expr := #[]
  for i in [:k] do
    let lt ← Lean.Meta.mkLt (Lean.mkNatLit i) (Lean.mkNatLit k)
    let fin := Lean.mkApp3 (Lean.mkConst ``Fin.mk) (Lean.mkNatLit k) (Lean.mkNatLit i) (←Lean.Meta.mkDecideProof lt)
    symbols := symbols.push (←Lean.Meta.whnf (Lean.mkApp parameters fin))
  let term ← reify k symbols value
  let proof := Lean.mkAppN (Lean.mkConst ``Certificate.mk) #[kExpr,parameters,value,term,←Lean.Meta.mkEqRefl value]
  goal.assign proof
  Lean.Elab.Tactic.replaceMainGoal []

end BuyAtBulk.Computation.Runtime.PolynomialBudget
