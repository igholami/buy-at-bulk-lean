import BuyAtBulk.EdgeOnlyGap.Items.Exposure

import BuyAtBulk.EdgeOnlyGap.Items.AdaptivePolicy

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 2: execute at most T fresh adaptive matching queries. -/
def adaptiveTranscript (H : FiniteGraph) (q T : ℕ) (policy : AdaptivePolicy H q T)
    (π : Lift H q) : ℕ → List (Exposure H q)
  | 0 => []
  | k+1 =>
    let hist := adaptiveTranscript H q T policy π k
    if hist.length < T then match policy.next hist with
      | none => hist
      | some (e,rev,j) => hist ++ [if rev then (e,(π e).symm j,j) else (e,j,π e j)]
    else hist

end BuyAtBulk.EdgeOnlyGap
