import BuyAtBulk.Computation.Runtime.RoundingRefinement
open BuyAtBulk.Computation BuyAtBulk.Computation.Runtime

namespace ZeroRentalRegression

def freePair : ShortestPath.GraphEncoding 3 where
  adjacency := #v[#v[false,true,false],#v[true,false,false],#v[false,false,false]]
  symmetric := by decide
  diagonal := by decide

-- Original counterexample: B=1, but deleting positive-length vertex 2 gives B0=0.
/-- info: some [true, true, false] -/
#guard_msgs in
#eval (StoredRounding.run freePair #v[0,0,1] #v[0,0,1] #v[1,1,1]
  1 #v[0] #v[1] #v[0] 8 1 (by decide)).value.map fun output => output.bought.toList

-- Positive restricted budget: only the zero-physical path may be purchased.
def paidZeroPair : ShortestPath.GraphEncoding 4 where
  adjacency := #v[#v[false,true,false,false],#v[true,false,true,false],
    #v[false,true,false,false],#v[false,false,false,false]]
  symmetric := by decide
  diagonal := by decide

/-- info: some [true, true, true, false] -/
#guard_msgs in
#eval (StoredRounding.run paidZeroPair #v[0,1,0,9] #v[0,0,0,9] #v[1,1,1,1]
  10 #v[0] #v[2] #v[0] 8 1 (by decide)).value.map fun output => output.bought.toList

-- An empty zero phase buys nothing, including fully open paid vertices.
/-- info: some [false, false, false] -/
#guard_msgs in
#eval (StoredRounding.zeroRun freePair #v[0,0,1] #v[0,0,1] #v[1,1,1]
  1 #v[0] #v[1] #v[1]).value.map fun output => output.1.bought.toList

-- An empty positive phase returns its seed without constructing a helper.
/-- info: some [true, true, false] -/
#guard_msgs in
#eval (StoredRounding.positiveRun freePair #v[0,0,1] #v[0,0,1] #v[1,1,1]
  1 #v[0] #v[1] #v[0] 8 1 #v[true,true,false] (by decide)).value.map fun output => output.1.bought.toList

-- A mixed instance exercises both phase projections and request coverage.
def mixedPairs : ShortestPath.GraphEncoding 5 where
  adjacency := #v[#v[false,true,false,false,false],#v[true,false,false,false,false],
    #v[false,false,false,true,false],#v[false,false,true,false,true],
    #v[false,false,false,true,false]]
  symmetric := by decide
  diagonal := by decide

/-- info: some ([true, true, true, true, true], [0, 1]) -/
#guard_msgs in
#eval (StoredRounding.run mixedPairs #v[0,0,0,1,0] #v[0,0,0,1,0] #v[1,1,1,1,1]
  1 #v[0,2] #v[1,4] #v[0,1] 8 1 (by decide)).value.map fun output =>
    (output.bought.toList, output.routes.map fun entry => entry.1.val)

end ZeroRentalRegression
