import BuyAtBulk.Computation.Runtime.SparseSuppliedDecompose
import BuyAtBulk.Computation.Runtime.SparseSuppliedOutput
import BuyAtBulk.Computation.Runtime.SparseSuppliedRun
open BuyAtBulk.Computation BuyAtBulk.Computation.Runtime

namespace SparseSuppliedSmoke

def pair : ShortestPath.GraphEncoding 2 where
  adjacency := #v[#v[false,true],#v[true,false]]
  symmetric := by decide
  diagonal := by decide

def edgePath : pair.graph.Path 0 1 :=
  ⟨.cons (by decide) .nil, by simp⟩

-- Distinct rational entries on the same path merge to one unit-weight path.
/-- info: some [(1, [0, 1])] -/
#guard_msgs in
#eval (SparseSupplied.compress pair [(1/3,edgePath),(2/3,edgePath)]).value.map
  fun entries => entries.map fun e => (e.1,e.2.val.support.map Fin.val)

-- Coincident endpoints retain the singleton vertex and full unit mass.
def trivialPath : pair.graph.Path 0 0 := ⟨.nil,by simp⟩
/-- info: some [(1, [0])] -/
#guard_msgs in
#eval (SparseSupplied.compress pair [(1/4,trivialPath),(3/4,trivialPath)]).value.map
  fun entries => entries.map fun e => (e.1,e.2.val.support.map Fin.val)

-- These two simple paths create an opposing-arc circulation between 1 and 2.
def diamond : ShortestPath.GraphEncoding 4 where
  adjacency := #v[#v[false,true,true,false],#v[true,false,true,true],
    #v[true,true,false,true],#v[false,true,true,false]]
  symmetric := by decide
  diagonal := by decide

def leftPath : diamond.graph.Path 0 3 :=
  ⟨.cons (show diamond.graph.Adj 0 1 by decide)
    (.cons (show diamond.graph.Adj 1 2 by decide) (.cons (by decide) .nil)),by simp⟩
def rightPath : diamond.graph.Path 0 3 :=
  ⟨.cons (show diamond.graph.Adj 0 2 by decide)
    (.cons (show diamond.graph.Adj 2 1 by decide) (.cons (by decide) .nil)),by simp⟩
/-- info: some [(1 / 2, [0, 1, 3]), (1 / 2, [0, 2, 3])] -/
#guard_msgs in
#eval (SparseSupplied.compress diamond [(1/2,leftPath),(1/2,rightPath)]).value.map
  fun entries => entries.map fun e => (e.1,e.2.val.support.map Fin.val)

-- Empty request families flatten to no stored entries.
/-- info: 0 -/
#guard_msgs in
#eval (SparseSupplied.flattenFamily (G:=pair.graph) (fun i : Fin 0 => i.elim0)
  (fun i : Fin 0 => i.elim0) (fun i => i.elim0)).length

-- Full indexed traversal groups interleaved duplicate entries by request.
def source : Fin 2 → Fin 2 := fun _ => 0
def target : Fin 2 → Fin 2 := fun _ => 1
def interleaved : List (StoredOriginal.Entry (G:=pair.graph) source target) :=
  [⟨1,(1/3,edgePath)⟩,⟨0,(1/4,edgePath)⟩,⟨1,(2/3,edgePath)⟩,⟨0,(3/4,edgePath)⟩]
/-- info: some [(0, 1, [0, 1]), (1, 1, [0, 1])] -/
#guard_msgs in
#eval (SparseSupplied.run source target pair interleaved).value.map fun entries =>
  entries.map fun e => (e.1.val,e.2.1,e.2.2.val.support.map Fin.val)

-- The full runner succeeds on an empty request family.
/-- info: some 0 -/
#guard_msgs in
#eval (SparseSupplied.run (fun i : Fin 0 => (i.elim0 : Fin 2))
  (fun i : Fin 0 => (i.elim0 : Fin 2)) pair []).value.map List.length

end SparseSuppliedSmoke
