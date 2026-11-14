import BuyAtBulk.EdgeOnlyGap.Items.PortTable

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit port enumeration, p. 2. -/
theorem portsExist (H : FiniteGraph) (d : ℕ) (degree : ∀ v, H.graph.degree v ≤ d) :
  Nonempty (PortTable H d) := by
  classical
  let Inc (v : Fin H.n) := {e : Edges H // v = e.val.1 ∨ v = e.val.2}
  let toN (v : Fin H.n) (x : Inc v) : H.graph.neighborSet v :=
    if h : v = x.val.val.1 then
      ⟨x.val.val.2, by
        rw [SimpleGraph.mem_neighborSet]
        simpa only [h] using x.val.prop.2⟩
    else
      ⟨x.val.val.1, by
        have h2 : v = x.val.val.2 := x.prop.resolve_left h
        rw [SimpleGraph.mem_neighborSet]
        simpa only [h2] using x.val.prop.2.symm⟩
  have hInj : ∀ v, Function.Injective (toN v) := by
    intro v x y hxy
    have hval := congrArg Subtype.val hxy
    dsimp [toN] at hval
    split_ifs at hval with hx hy hy
    · apply Subtype.ext; apply Subtype.ext; apply Prod.ext
      · exact hx.symm.trans hy
      · exact hval
    · have hy2 : v = y.val.val.2 := y.prop.resolve_left hy
      have hxlt : x.val.val.1 < x.val.val.2 := x.val.prop.1
      have hylt : y.val.val.1 < y.val.val.2 := y.val.prop.1
      exfalso
      have h1 : v < y.val.val.1 := hx.trans_lt (hxlt.trans_eq hval)
      have h2 : y.val.val.1 < v := hylt.trans_eq hy2.symm
      exact lt_asymm h1 h2
    · have hx2 : v = x.val.val.2 := x.prop.resolve_left hx
      have hxlt : x.val.val.1 < x.val.val.2 := x.val.prop.1
      have hylt : y.val.val.1 < y.val.val.2 := y.val.prop.1
      exfalso
      have h1 : x.val.val.1 < v := hxlt.trans_eq hx2.symm
      have h2 : v < x.val.val.1 := hy.trans_lt (hylt.trans_eq hval.symm)
      exact lt_asymm h1 h2
    · have hx2 : v = x.val.val.2 := x.prop.resolve_left hx
      have hy2 : v = y.val.val.2 := y.prop.resolve_left hy
      apply Subtype.ext; apply Subtype.ext; apply Prod.ext
      · exact hval
      · exact hx2.symm.trans hy2
  have hCard : ∀ v, Fintype.card (Inc v) ≤ d := by
    intro v
    have h1 : Fintype.card (Inc v) ≤ Fintype.card (H.graph.neighborSet v) :=
      Fintype.card_le_of_injective (toN v) (hInj v)
    rw [H.graph.card_neighborSet_eq_degree] at h1
    exact le_trans h1 (degree v)
  let eqv (v : Fin H.n) := Fintype.equivFin (Inc v)
  refine ⟨{
    port := fun v p =>
      if h : p.val < Fintype.card (Inc v) then
        some ((eqv v).symm ⟨p.val, h⟩).val
      else none
    incident := by
      intro v p e hp
      by_cases h : p.val < Fintype.card (Inc v)
      · rw [dif_pos h] at hp
        injection hp with hp'
        rw [← hp']
        exact ((eqv v).symm ⟨p.val, h⟩).prop
      · rw [dif_neg h] at hp
        contradiction
    injective := by
      intro v p p' e hp hp'
      by_cases h : p.val < Fintype.card (Inc v)
      · rw [dif_pos h] at hp
        by_cases h' : p'.val < Fintype.card (Inc v)
        · rw [dif_pos h'] at hp'
          injection hp with hp1
          injection hp' with hp2
          have heq : (eqv v).symm ⟨p.val, h⟩ = (eqv v).symm ⟨p'.val, h'⟩ :=
            Subtype.ext (hp1.trans hp2.symm)
          have hfin := (eqv v).symm.injective heq
          exact Fin.ext (congrArg (fun z : Fin (Fintype.card (Inc v)) => z.val) hfin)
        · rw [dif_neg h'] at hp'
          contradiction
      · rw [dif_neg h] at hp
        contradiction
    complete := by
      intro v e he
      let i := eqv v ⟨e, he⟩
      have hi : i.val < Fintype.card (Inc v) := i.isLt
      refine ⟨⟨i.val, lt_of_lt_of_le hi (hCard v)⟩, ?_⟩
      change (if h : i.val < Fintype.card (Inc v) then some ((eqv v).symm ⟨i.val, h⟩).val else none) = some e
      rw [dif_pos hi]
      congr 1
      exact congrArg Subtype.val ((eqv v).symm_apply_apply ⟨e, he⟩)
  }⟩

end BuyAtBulk.EdgeOnlyGap
