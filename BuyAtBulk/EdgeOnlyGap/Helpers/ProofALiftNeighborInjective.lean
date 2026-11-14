import BuyAtBulk.EdgeOnlyGap.Items.LiftCovering

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA

/-- Projection is injective on each lifted vertex's neighbors, by matching uniqueness. -/
theorem liftNeighborInjective (H : FiniteGraph) (q : ℕ) (π : Lift H q)
    (v x y : Fin H.n × Fin q)
    (hx : (liftGraph H q π).Adj v x) (hy : (liftGraph H q π).Adj v y)
    (hxy : x.1 = y.1) : x = y := by
  have hbase : H.graph.Adj v.1 x.1 := by
    unfold liftGraph at hx
    rw [SimpleGraph.fromRel_adj] at hx
    rcases hx with ⟨_, ⟨e, hv, hx, _⟩ | ⟨e, hv, hx, _⟩⟩
    · rw [hv, hx]; exact e.prop.2
    · rw [hv, hx]; exact e.prop.2.symm
  have hm := (liftCovering H q π).2.2.2
  apply Prod.ext hxy
  rcases lt_or_gt_of_ne hbase.ne with hlt | hgt
  · let e : Edges H := ⟨(v.1, x.1), hlt, hbase⟩
    have hx' : x.2 = π e v.2 := (hm e v.2 x.2).mp hx
    have hy' : y.2 = π e v.2 := by
      apply (hm e v.2 y.2).mp
      change (liftGraph H q π).Adj v (x.1, y.2)
      rw [hxy]
      exact hy
    exact hx'.trans hy'.symm
  · let e : Edges H := ⟨(x.1, v.1), hgt, hbase.symm⟩
    have hx' : v.2 = π e x.2 := (hm e x.2 v.2).mp hx.symm
    have hy' : v.2 = π e y.2 := by
      apply (hm e y.2 v.2).mp
      change (liftGraph H q π).Adj (x.1, y.2) v
      rw [hxy]
      exact hy.symm
    exact (π e).injective (hx'.symm.trans hy')

end BuyAtBulk.EdgeOnlyGap.ProofA
