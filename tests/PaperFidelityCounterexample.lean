import BuyAtBulk.Computation.Runtime.RoundingRefinement
open BuyAtBulk.Computation BuyAtBulk.Computation.Runtime

def fidelityGraph : ShortestPath.GraphEncoding 3 where
  adjacency := #v[#v[false,true,false],#v[true,false,false],#v[false,false,false]]
  symmetric := by decide
  diagonal := by decide

-- Regression: the positive-physical isolated vertex is excluded.
/-- info: some [true, true, false] -/
#guard_msgs in
#eval (StoredRounding.run fidelityGraph #v[0,0,1] #v[0,0,1] #v[1,1,1]
  1 #v[0] #v[1] #v[0] 8 1 (by decide)).value.map fun output => output.bought.toList
