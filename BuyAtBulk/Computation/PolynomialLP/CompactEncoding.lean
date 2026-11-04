import BuyAtBulk.Computation.PolynomialLP.Optimization
import BuyAtBulk.Model.CompactFlowOptimizer
import Mathlib.Logic.Equiv.Fin.Basic

/-! Literal dense encoding of the paper's compact flow LP. Finite sum/product
numberings use arithmetic equivalences, with no chosen finite enumeration. -/
namespace BuyAtBulk.PolynomialLP.CompactEncoding
open CompactFlow

def variableCount (n h : ℕ) := n+(h*n+h*(n*n))
def constraintCount (n h : ℕ) := 2*variableCount n h+(h*n+((2*2)*(h*n)+h*(n*n)))

def variableEquiv (n h : ℕ) : VariableIndex (Fin n) h ≃ Fin (variableCount n h) :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr finProdFinEquiv
    ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv))).trans
      ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv)

def constraints (n h : ℕ) : ConstraintIndex (Fin n) h ≃ Fin (constraintCount n h) :=
  (Equiv.sumCongr
    ((Equiv.prodCongr finTwoEquiv.symm (variableEquiv n h)).trans finProdFinEquiv)
    ((Equiv.sumCongr finProdFinEquiv
      ((Equiv.sumCongr
        ((Equiv.prodCongr
          ((Equiv.prodCongr finTwoEquiv.symm finTwoEquiv.symm).trans finProdFinEquiv)
          finProdFinEquiv).trans finProdFinEquiv)
        ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv

structure Data (n h : ℕ) where
  adjacency : Vector (Vector Bool n) n
  source : Vector (Fin n) h
  target : Vector (Fin n) h
  buying : Vector ℚ n
  physical : Vector ℚ n
  demand : Vector ℚ h

variable {n h : ℕ}

def nodeCoefficient (i : Fin h) (v : Fin n) : VariableIndex (Fin n) h → ℚ
  | .inr (.inl (j,w)) => if i=j ∧ v=w then 1 else 0
  | _ => 0

def openingCoefficient (v : Fin n) : VariableIndex (Fin n) h → ℚ
  | .inl w => if v=w then 1 else 0
  | _ => 0

def balanceCoefficient (incoming : Bool) (i : Fin h) (v : Fin n)
    (c : VariableIndex (Fin n) h) : ℚ :=
  let transport : ℚ := match c with
    | .inr (.inr (j,u,w)) => if i=j ∧ (if incoming then v=w else v=u) then 1 else 0
    | _ => 0
  if incoming then nodeCoefficient i v c-transport else transport-nodeCoefficient i v c

def coefficient (data : Data n h) : ConstraintIndex (Fin n) h → VariableIndex (Fin n) h → ℚ
  | .inl (upper,c), d => (if upper then 1 else -1)*(if c=d then 1 else 0)
  | .inr (.inl (i,v)), c => nodeCoefficient i v c-openingCoefficient v c
  | .inr (.inr (.inl ((positive,incoming),(i,v)))), c =>
      (if positive then 1 else -1)*balanceCoefficient incoming i v c
  | .inr (.inr (.inr (i,u,v))), c =>
      if data.adjacency[u.val][v.val] then 0 else if c=Sum.inr (Sum.inr (i,u,v)) then 1 else 0

def bound (data : Data n h) : ConstraintIndex (Fin n) h → ℚ
  | .inl (upper,_) => if upper then 1 else 0
  | .inr (.inl _) => 0
  | .inr (.inr (.inl ((positive,incoming),(i,v)))) =>
      (if positive then 1 else -1)*
      (if incoming then (if data.source[i.val]=v then 1 else 0)
        else -(if data.target[i.val]=v then 1 else 0))
  | .inr (.inr (.inr _)) => 0

def objective (data : Data n h) : VariableIndex (Fin n) h → ℚ
  | .inl v => data.buying[v.val]
  | .inr (.inl (i,v)) => data.demand[i.val]*data.physical[v.val]
  | .inr (.inr _) => 0

def stored (data : Data n h) : Stored (n := variableCount n h) (m := constraintCount n h) where
  coefficients := Vector.ofFn fun i => Vector.ofFn fun j =>
    coefficient data ((constraints n h).symm i) ((variableEquiv n h).symm j)
  bounds := Vector.ofFn fun i => bound data ((constraints n h).symm i)
  objective := Vector.ofFn fun j => objective data ((variableEquiv n h).symm j)

end BuyAtBulk.PolynomialLP.CompactEncoding
