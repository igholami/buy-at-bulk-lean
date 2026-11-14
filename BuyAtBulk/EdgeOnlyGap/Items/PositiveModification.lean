import BuyAtBulk.EdgeOnlyGap.Items.RoutingStatistics

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 5: core buying and spoke lengths changed to 1/h; other data preserved. -/
def positiveData (H : FiniteGraph) (q d : ℕ) (π : Lift H q) (hd : 0 < d) :
    BuyAtBulk.GraphData := by
  classical
  let D := supplyData H q d π hd
  exact { D with
    buying := fun a => if coreResource H q d π hd a then 1/(requests H:ℚ) else D.buying a
    length := fun a => if coreResource H q d π hd a then D.length a else 1/(requests H:ℚ)
    buying_nonneg := by
      intro a
      split_ifs
      · exact div_nonneg (by norm_num) (Nat.cast_nonneg _)
      · exact D.buying_nonneg a
    length_nonneg := by
      intro a
      split_ifs
      · exact D.length_nonneg a
      · exact div_nonneg (by norm_num) (Nat.cast_nonneg _) }

end BuyAtBulk.EdgeOnlyGap
