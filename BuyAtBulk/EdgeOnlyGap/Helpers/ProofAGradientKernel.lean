import BuyAtBulk.EdgeOnlyGap.Items.Boundary
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

/-- The transpose of the binary boundary, on vertex labels. -/
def gradient (H : FiniteGraph) (W : Finset (Edges H)) :
    (Fin H.n → ZMod 2) →ₗ[ZMod 2] ({e // e ∈ W} → ZMod 2) where
  toFun x e := x e.val.val.1 + x e.val.val.2
  map_add' x y := by ext e; simp; ring
  map_smul' c x := by ext e; simp [mul_add]

/-- Kernel labels are exactly labels of connected components, including isolated vertices. -/
def gradientKernelEquiv (H : FiniteGraph) (W : Finset (Edges H)) :
    ((edgeSubgraph H W).ConnectedComponent → ZMod 2) ≃ₗ[ZMod 2]
      LinearMap.ker (gradient H W) := by
  classical
  let f : ((edgeSubgraph H W).ConnectedComponent → ZMod 2) →ₗ[ZMod 2]
      (Fin H.n → ZMod 2) :=
    { toFun := fun x v => x ((edgeSubgraph H W).connectedComponentMk v)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : ∀ x, f x ∈ LinearMap.ker (gradient H W) := by
    intro x
    ext e
    have h : (edgeSubgraph H W).connectedComponentMk e.val.val.1 =
        (edgeSubgraph H W).connectedComponentMk e.val.val.2 := by
      apply SimpleGraph.ConnectedComponent.eq.mpr
      apply SimpleGraph.Adj.reachable
      rw [edgeSubgraph, SimpleGraph.fromRel_adj]
      exact ⟨ne_of_lt e.val.prop.1, Or.inl ⟨e.val, e.prop, rfl, rfl⟩⟩
    change x ((edgeSubgraph H W).connectedComponentMk e.val.val.1) +
      x ((edgeSubgraph H W).connectedComponentMk e.val.val.2) = 0
    rw [h, CharTwo.add_self_eq_zero]
  let fk := f.codRestrict (LinearMap.ker (gradient H W)) hf
  apply LinearEquiv.ofBijective fk
  constructor
  · intro x y h
    ext c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h v => exact congrFun (congrArg Subtype.val h) v
  · intro x
    have hadj : ∀ {u v}, (edgeSubgraph H W).Adj u v → x.val u = x.val v := by
      intro u v huv
      rw [edgeSubgraph, SimpleGraph.fromRel_adj] at huv
      rcases huv.2 with ⟨e, he, rfl, rfl⟩ | ⟨e, he, rfl, rfl⟩
      · have hz := congrFun x.prop ⟨e, he⟩
        change x.val e.val.1 + x.val e.val.2 = 0 at hz
        exact (eq_neg_of_add_eq_zero_left hz).trans (CharTwo.neg_eq _)
      · have hz := congrFun x.prop ⟨e, he⟩
        change x.val e.val.1 + x.val e.val.2 = 0 at hz
        exact ((eq_neg_of_add_eq_zero_left hz).trans (CharTwo.neg_eq _)).symm
    have hwalk : ∀ {u v} (p : (edgeSubgraph H W).Walk u v), x.val u = x.val v := by
      intro u v p
      induction p with
      | nil => rfl
      | cons h _ ih => exact (hadj h).trans ih
    refine ⟨SimpleGraph.ConnectedComponent.lift x.val (fun _ _ p _ => hwalk p), ?_⟩
    apply Subtype.ext
    funext v
    rfl

end BuyAtBulk.EdgeOnlyGap.ProofA
