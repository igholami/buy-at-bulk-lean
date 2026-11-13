import BuyAtBulk.EdgeOnlyGap.Items.PortBoundary

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 4: Z consists of used-edge chains with zero port boundary. -/
def portKernel (H : FiniteGraph) (q d : ℕ) (π : Lift H q) (hd : 0 < d)
    (r : (supplyData H q d π hd).toInstance.IntegralRouting) :=
  (portBoundary H q d π hd r).ker

end BuyAtBulk.EdgeOnlyGap
