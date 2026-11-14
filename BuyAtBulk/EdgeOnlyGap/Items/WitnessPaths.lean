import BuyAtBulk.EdgeOnlyGap.Items.SupplyData

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 3: q simple matching-induced three-edge paths. -/
def witnessPath (H : FiniteGraph) (q : ℕ) (π : Lift H q) (e : Edges H) (j : Fin q) :
    (supplyGraph H q π).Path (Sum.inl e.val.1) (Sum.inl e.val.2) := by
  let G := supplyGraph H q π
  let a : SupplyVertex H q := Sum.inr (e.val.1,j)
  let b : SupplyVertex H q := Sum.inr (e.val.2,π e j)
  have ha : G.Adj (Sum.inl e.val.1) a := by
    dsimp [G, supplyGraph]
    rw [SimpleGraph.fromRel_adj]
    refine ⟨by simp [a], Or.inl (Or.inl ⟨e.val.1, j, rfl, rfl⟩)⟩
  have hb : G.Adj a b := by
    dsimp [G, supplyGraph]
    rw [SimpleGraph.fromRel_adj]
    have hne : a ≠ b := by
      intro h
      have h1 : e.val.1 = e.val.2 := congrArg Prod.fst (Sum.inr.inj h)
      exact ne_of_lt e.prop.1 h1
    refine ⟨hne, Or.inl (Or.inr ⟨(e.val.1, j), (e.val.2, π e j), rfl, rfl, ?_⟩)⟩
    dsimp [liftGraph]
    rw [SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl ⟨e, rfl, rfl, rfl⟩⟩
    intro h
    have h1 : e.val.1 = e.val.2 := congrArg Prod.fst h
    exact ne_of_lt e.prop.1 h1
  have hc : G.Adj b (Sum.inl e.val.2) := by
    dsimp [G, supplyGraph]
    rw [SimpleGraph.fromRel_adj]
    refine ⟨by simp [b], Or.inr (Or.inl ⟨e.val.2, π e j, rfl, rfl⟩)⟩
  refine ⟨.cons ha (.cons hb (.cons hc .nil)), ?_⟩
  rw [SimpleGraph.Walk.isPath_def]
  simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.nodup_cons,
    List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · simp [a]
  · simp [b]
  · intro h
    exact ne_of_lt e.prop.1 (Sum.inl.inj h)
  · intro h
    have h1 : e.val.1 = e.val.2 := congrArg Prod.fst (Sum.inr.inj h)
    exact ne_of_lt e.prop.1 h1
  · simp [a]
  · simp [b]

end BuyAtBulk.EdgeOnlyGap
