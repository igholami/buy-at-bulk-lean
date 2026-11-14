import BuyAtBulk.Model.GraphInstance
import BuyAtBulk.EdgeOnlyGap.Items.SupplyGraph
import BuyAtBulk.EdgeOnlyGap.Items.Parameters

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 3: canonical all-simple-path LP, one resource per supply edge. Zero core buying and zero spoke lengths. -/
def supplyData (H : FiniteGraph) (q d : ℕ) (π : Lift H q) (hd : 0 < d) :
    BuyAtBulk.GraphData := by
  classical
  let G := supplyGraph H q π
  let E := G.edgeSet
  let enum := (Fintype.equivFin E).symm
  let req := (Fintype.equivFin (Edges H)).symm
  exact {
    Vertex := SupplyVertex H q
    vertexFintype := inferInstance
    graph := G
    resourceCount := Fintype.card E
    requestCount := requests H
    source := fun i => Sum.inl (req i).val.1
    target := fun i => Sum.inl (req i).val.2
    location := fun a => Sum.inr (enum a).val
    location_injective := by
      intro a b hab
      apply enum.injective
      exact Subtype.ext (Sum.inr.inj hab)
    location_valid := by
      intro a
      exact (enum a).property
    buying := fun a => if ∃ v w : Fin H.n × Fin q,
      (enum a).val = s(Sum.inr v, Sum.inr w) then 0 else 1
    length := fun a => if ∃ v w : Fin H.n × Fin q,
      (enum a).val = s(Sum.inr v, Sum.inr w) then 2 / (d : ℚ) else 0
    demand := fun _ => 1
    buying_nonneg := by
      intro a
      split_ifs <;> norm_num
    length_nonneg := by
      intro a
      split_ifs
      · exact div_nonneg (by norm_num) (Nat.cast_nonneg d)
      · norm_num
    demand_pos := by
      intro _
      norm_num }

end BuyAtBulk.EdgeOnlyGap
