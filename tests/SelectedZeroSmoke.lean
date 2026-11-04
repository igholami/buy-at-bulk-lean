import BuyAtBulk.Computation.Rounding.SelectedZero
import BuyAtBulk.Computation.ShortestPath.Encoding
open BuyAtBulk.Computation

namespace SelectedZeroSmoke

def graphInput : ShortestPath.GraphEncoding 3 where
  adjacency := #v[#v[false,true,false],#v[true,false,false],#v[false,false,false]]
  symmetric := by decide
  diagonal := by decide

def run (budget : ℚ) (selected : Finset (Fin 2)) :=
  Rounding.selectedZeroRun graphInput.graph (Equiv.refl _) (fun v => if v=2 then 1 else 0)
    (fun v => if v=2 then 1 else 0) (fun _ => 1) budget
    (fun _ : Fin 2 => (0 : Fin 3)) (fun _ => 1) (fun _ => 0) selected

-- Strict subset retains its original index and excludes the positive-length vertex.
/-- info: some ([0, 1], [1]) -/
#guard_msgs in
#eval (run 1 {1}).map fun output => (((List.finRange 3).filter fun v => v ∈ output.bought).map Fin.val,
  output.routes.map fun entry => entry.1.val)

-- Empty subsets have no purchases and no routes.
/-- info: some ([], []) -/
#guard_msgs in
#eval (run 1 ∅).map fun output => (((List.finRange 3).filter fun v => v ∈ output.bought).map Fin.val,
  output.routes.map fun entry => entry.1.val)

-- Zero total budget selects the same free actual route.
/-- info: some ([0, 1], [1]) -/
#guard_msgs in
#eval (run 0 {1}).map fun output => (((List.finRange 3).filter fun v => v ∈ output.bought).map Fin.val,
  output.routes.map fun entry => entry.1.val)

end SelectedZeroSmoke
