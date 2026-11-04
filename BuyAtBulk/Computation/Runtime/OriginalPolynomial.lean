import BuyAtBulk.Computation.Runtime.OriginalRuntime
import BuyAtBulk.Computation.Runtime.OriginalEncodingBridge

/-! A uniform polynomial bound for the fully closed graph-only approximation
program, measured in an explicit signed-integer-array binary input encoding. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 65536
namespace BuyAtBulk.Computation.Runtime.Original
open Rational BuyAtBulk.Computation.StoredOriginal PolynomialBudget
namespace Polynomial

open Lean Meta Elab Tactic in
private partial def reifyOriginal (cache : IO.Ref (Std.HashMap Lean.Expr Lean.Expr)) (k : ℕ) (symbols : Array Lean.Expr) (value : Lean.Expr) : MetaM Lean.Expr := do
  let value := value.consumeMData
  if let some term := (←cache.get)[value]? then return term
  let result ← do
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
        (←reifyOriginal cache k symbols args[args.size-2]!) (←reifyOriginal cache k symbols args[args.size-1]!)
    if name == some ``Nat.mul || name == some ``HMul.hMul then
      return mkApp3 (mkConst ``Term.times) (mkNatLit k)
        (←reifyOriginal cache k symbols args[args.size-2]!) (←reifyOriginal cache k symbols args[args.size-1]!)
    if name == some ``Nat.pow || name == some ``HPow.hPow || name == some ``Pow.pow then
      let exponent ← whnf args[args.size-1]!
      if let some n ← getNatValue? exponent then
        return mkApp3 (mkConst ``Term.power) (mkNatLit k)
          (←reifyOriginal cache k symbols args[args.size-2]!) (mkNatLit n)
      throwError "original polynomial exponent must be fixed"
    if name == some ``Nat.succ then
      return mkApp3 (mkConst ``Term.plus) (mkNatLit k) (←reifyOriginal cache k symbols args[0]!)
        (mkApp2 (mkConst ``Term.constant) (mkNatLit k) (mkNatLit 1))
    if name == some ``List.sum then
      let rec listTerm (items : Lean.Expr) : MetaM Lean.Expr := do
        let items ← whnf items
        if items.isAppOf ``List.nil then
          return mkApp2 (mkConst ``Term.constant) (mkNatLit k) (mkNatLit 0)
        if items.isAppOf ``List.cons then
          let parts := items.getAppArgs
          return mkApp3 (mkConst ``Term.plus) (mkNatLit k)
            (←reifyOriginal cache k symbols parts[parts.size-2]!) (←listTerm parts[parts.size-1]!)
        throwError "original polynomial list sum must have fixed finite spine"
      return ← listTerm args[args.size-1]!
    if let some unfolded ← delta? value then return ← reifyOriginal cache k symbols unfolded
    let reduced ← whnf value
    if reduced != value then return ← reifyOriginal cache k symbols reduced
    throwError "unsupported original polynomial expression: {value}"
  cache.modify fun entries => entries.insert value result
  return result

elab "original_poly_cert" : tactic => Lean.Elab.Tactic.withMainContext do
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
  let term ← reifyOriginal cache k symbols value
  goal.assign (Lean.mkAppN (Lean.mkConst ``Certificate.mk)
    #[kExpr,parameters,value,term,←Lean.Meta.mkEqRefl value])
  Lean.Elab.Tactic.replaceMainGoal []


def parameters (n r h m L : ℕ) (i : Fin 5) : ℕ :=
  if i=0 then n else if i=1 then r else if i=2 then h else if i=3 then m else L

def countCertificate (n r h m L : ℕ) : Certificate (parameters n r h m L) (computationCount n r h m L+3) := by original_poly_cert

def wordsCertificate (n r h m L : ℕ) : Certificate (parameters n r h m L) (computationWords n r h m L) := by original_poly_cert

def countTerm : Term 5 := (countCertificate 0 0 0 0 0).term

def wordsTerm : Term 5 := (wordsCertificate 0 0 0 0 0).term

private theorem term_bound (term : Term 5) (n r h m L S : ℕ)
    (nBound : n≤S) (rBound : r≤S) (hBound : h≤S) (mBound : m≤4*S) (LBound : L≤S+8) :
    term.eval (parameters n r h m L)≤(term.weight*9^term.degree)*(S+1)^term.degree := by
  have inputs : ∀ i,parameters n r h m L i≤8*(S+1) := by
    intro i
    simp only[parameters]
    split_ifs <;>omega
  have base : 8*(S+1)+1≤9*(S+1) := by omega
  calc
    _ ≤ term.weight*(8*(S+1)+1)^term.degree := term.eval_le _ _ inputs
    _ ≤ term.weight*(9*(S+1))^term.degree := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left base _)
    _ = _ := by rw[mul_pow];ring

variable {n resources requests : ℕ} (tables : Tables n resources requests)

private theorem reduced_bound : (cachedBuffers tables).value.count≤4*inputSize tables := by
  rw[cachedBuffers_count_value]
  have reduced : reducedCount tables≤n+n*n+2*requests :=
    BuyAtBulk.Computation.NodeReduction.numbering_size tables.graphData (Equiv.refl _)
  have vertices := inputSize_vertices tables
  have square := inputSize_square tables
  have requests := inputSize_requests tables
  omega

private theorem count_payload :
    computationCount n resources requests (cachedBuffers tables).value.count (originalLeafBudget tables)+3≤
      (countTerm.weight*9^countTerm.degree)*(inputSize tables+1)^countTerm.degree := by
  exact (countCertificate n resources requests (cachedBuffers tables).value.count (originalLeafBudget tables)).correct.symm.trans_le
    (term_bound countTerm _ _ _ _ _ _ (inputSize_vertices tables) (inputSize_resources tables)
      (inputSize_requests tables) (reduced_bound tables) (by dsimp[originalLeafBudget];omega))

private theorem words_payload :
    computationWords n resources requests (cachedBuffers tables).value.count (originalLeafBudget tables)≤
      (wordsTerm.weight*9^wordsTerm.degree)*(inputSize tables+1)^wordsTerm.degree := by
  exact (wordsCertificate n resources requests (cachedBuffers tables).value.count (originalLeafBudget tables)).correct.symm.trans_le
    (term_bound wordsTerm _ _ _ _ _ _ (inputSize_vertices tables) (inputSize_resources tables)
      (inputSize_requests tables) (reduced_bound tables) (by dsimp[originalLeafBudget];omega))

end Polynomial

/-- Fixed constants for the actual graph-only program. The input measure is
an explicit prefix-coded array containing dimensions, all adjacency cells,
resource locations, endpoints, and every rational price and demand field.
The event semantics is Primitive's rational/integer word-operation model. -/
def PolynomialGraphApproximationTarget : Prop :=
  ∃ C d W e : ℕ, ∀ (n resources requests : ℕ) (tables : Tables n resources requests),
    (closedTrace tables).value=closedRun tables ∧
    ClosedSpec tables (closedTrace tables).value ∧
    (closedTrace tables).events.length≤C*(OriginalEncoding.inputSize tables+1)^d ∧
    WordsWithin (W*(OriginalEncoding.inputSize tables+1)^e) (closedTrace tables).events

/-- Complete correctness, operation count, and every intermediate word bound
for the named original graph computation, with one fixed polynomial for all
instances and no fractional solution supplied to the algorithm. -/
theorem polynomial_graph_approximation : PolynomialGraphApproximationTarget := by
  refine ⟨(Polynomial.countTerm.weight*9^Polynomial.countTerm.degree)*17^Polynomial.countTerm.degree,
    2*Polynomial.countTerm.degree,
    (Polynomial.wordsTerm.weight*9^Polynomial.wordsTerm.degree)*17^Polynomial.wordsTerm.degree,
    2*Polynomial.wordsTerm.degree,?_⟩
  intro n resources requests tables
  obtain ⟨value,count,words⟩ := closedTrace_runtime tables
  refine ⟨value,closedTrace_correct tables,?_,?_⟩
  · exact count.trans ((Polynomial.count_payload tables).trans
      (OriginalEncoding.payload_polynomial tables _ _))
  · exact words.mono ((Polynomial.words_payload tables).trans
      (OriginalEncoding.payload_polynomial tables _ _))

end BuyAtBulk.Computation.Runtime.Original
