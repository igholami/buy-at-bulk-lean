import BuyAtBulk.Computation.Runtime.FreeRounding
import BuyAtBulk.Computation.Runtime.ZeroPhaseOutput
import BuyAtBulk.Computation.Runtime.RouteEntries
import BuyAtBulk.Computation.Runtime.PositivePhase

/-! The complete stored node rounder, including empty requests, zero buying
budget, both positive-budget phases, and its actual projected route list. -/
namespace BuyAtBulk.Computation.Runtime.StoredRounding
open BuyAtBulk.UpperBound
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

def run (buying physical opening : Vector ℚ n) (budget : ℚ) (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (ratio r : ℕ) (ratio_ge : 2 ≤ ratio) : Traced (Option (Output input source target)) :=
  let empty := emit .natCompare [h.size,0] (decide (h=0))
  let emptyEvents := empty.events++[⟨Operation.branch,[1]⟩]
  if empty.value then
    let flags := constantVector n false 1
    ⟨some ⟨flags.value,[]⟩,emptyEvents++flags.events++[⟨.cons,[n.size,1]⟩]⟩
  else
    let free := zeroTest budget
    let freeEvents := emptyEvents++free.events++[⟨.branch,[1]⟩]
    if free.value then
      let answer := freeRun input buying physical source target lengths
      ⟨answer.value,freeEvents++answer.events⟩
    else
      let zero := zeroRun input buying physical opening budget source target lengths
      let zeroEvents := freeEvents++zero.events++[⟨.branch,[1]⟩]
      match zero.value with
      | none => ⟨none,zeroEvents⟩
      | some (zeroAfter,zeroEntries) =>
        let positive := positiveRun input buying physical opening budget source target lengths ratio r zeroAfter.bought ratio_ge
        let positiveEvents := zeroEvents++positive.events++[⟨.branch,[1]⟩]
        match positive.value with
        | none => ⟨none,positiveEvents⟩
        | some (after,entries) =>
          let projected := projectEntries input physical source target lengths zeroEntries
          let combined := appendEntries input source target projected.value entries
          ⟨some ⟨after.bought,combined.value⟩,positiveEvents++projected.events++combined.events++[⟨.cons,[n.size,h.size]⟩]⟩

end BuyAtBulk.Computation.Runtime.StoredRounding
