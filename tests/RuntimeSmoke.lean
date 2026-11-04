import BuyAtBulk.Computation.Runtime.OriginalRuntime
import BuyAtBulk.Computation.PolynomialLP.OptimizationRuntime
import BuyAtBulk.Computation.Runtime.FlowDecomposition
namespace RuntimeSmoke
open BuyAtBulk.Computation.StoredOriginal BuyAtBulk.Computation.Runtime.Original

def emptyTables : Tables 0 0 0 where
  adjacency:=Vector.replicate 0 (Vector.replicate 0 false)
  symmetric:=by intro u;exact Fin.elim0 u
  loopless:=by intro u;exact Fin.elim0 u
  source:=Vector.ofFn Fin.elim0
  target:=Vector.ofFn Fin.elim0
  location:=Vector.ofFn Fin.elim0
  location_injective:=by intro a;exact Fin.elim0 a
  location_valid:=by intro a;exact Fin.elim0 a
  buying:=Vector.replicate 0 0
  length:=Vector.replicate 0 0
  demand:=Vector.replicate 0 1
  buying_nonneg:=by intro a;exact Fin.elim0 a
  length_nonneg:=by intro a;exact Fin.elim0 a
  demand_pos:=by intro i;exact Fin.elim0 i

def disconnectedTables : Tables 2 0 1 where
  adjacency:=Vector.replicate 2 (Vector.replicate 2 false)
  symmetric:=by intros;simp
  loopless:=by intros;simp
  source:=Vector.replicate 1 0
  target:=Vector.replicate 1 1
  location:=Vector.ofFn Fin.elim0
  location_injective:=by intro a;exact Fin.elim0 a
  location_valid:=by intro a;exact Fin.elim0 a
  buying:=Vector.replicate 0 0
  length:=Vector.replicate 0 0
  demand:=Vector.replicate 1 1
  buying_nonneg:=by intro a;exact Fin.elim0 a
  length_nonneg:=by intro a;exact Fin.elim0 a
  demand_pos:=by intros;simp

/-- info: true -/
#guard_msgs in
#eval match (closedTrace emptyTables).value with
  | .error _ => false
  | .ok output => output.routes.isEmpty

/-- info: true -/
#guard_msgs in
#eval match (closedTrace disconnectedTables).value with
  | .error i => i.val == 0
  | .ok _ => false

open BuyAtBulk.PolynomialLP
private def emptyLP : Stored (n:=0) (m:=0) :=
  ⟨Vector.ofFn (fun i => Fin.elim0 i),#v[],#v[]⟩
private def impossibleLP : Stored (n:=0) (m:=1) := ⟨#v[#v[]],#v[-1],#v[]⟩
private def intervalLP : Stored (n:=1) (m:=1) := ⟨#v[#v[-1]],#v[-(1/3:ℚ)],#v[1]⟩
/-- info: true -/
#guard_msgs in
#eval (optimize emptyLP).isSome
/-- info: true -/
#guard_msgs in
#eval (optimize impossibleLP).isNone
/-- info: true -/
#guard_msgs in
#eval (optimize intervalLP).map (fun point => point[0]) == some (1/3:ℚ)

open BuyAtBulk.Computation BuyAtBulk.Computation.Runtime
private def twoVertices : ShortestPath.GraphEncoding 2 where
  adjacency := #v[#v[false,true],#v[true,false]]
  symmetric := by decide
  diagonal := by decide
private def unitArc : FlowDecomposition.FlowMatrix 2 := #v[#v[0,1],#v[0,0]]
/-- info: true -/
#guard_msgs in
#eval ((FlowExtract.decompose twoVertices unitArc 0 1).value.map fun entries =>
  entries.map fun e => (e.1,e.2.val.support.map Fin.val)) == some [(1,[0,1])]
/-- info: true -/
#guard_msgs in
#eval ((FlowExtract.decompose twoVertices (#v[#v[0,0],#v[0,0]]) 0 0).value.map fun entries =>
  entries.map fun e => (e.1,e.2.val.support.map Fin.val)) == some [(1,[0])]
end RuntimeSmoke
