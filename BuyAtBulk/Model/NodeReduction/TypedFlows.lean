import BuyAtBulk.Model.GraphInstance
import Mathlib.Data.Fintype.BigOperators

noncomputable section
namespace BuyAtBulk.NodeReduction
open scoped BigOperators
local instance typedFlowsDecEq (D : GraphData) : DecidableEq D.Vertex := Classical.decEq _
local instance typedFlowsDecRel (D : GraphData) : DecidableRel D.graph.Adj := Classical.decRel _

/-- Wrong-request path tags have zero flow, so a complete indexed incidence
LP equals its typed per-request all-simple-path formulation. -/
theorem weighted_request_sum (D : GraphData) (f : D.toInstance.FractionalSolution)
    (hf : D.toInstance.Feasible f) (i : Fin D.requestCount) (weight : D.TaggedPath → ℚ) :
    (∑ p, weight (D.decode p) * f.flow i p) =
      ∑ path : D.graph.Path (D.source i) (D.target i),
        weight ⟨i, path⟩ * f.flow i (D.encode i path) := by
  classical
  calc
    _ = ∑ tagged : D.TaggedPath, weight tagged * f.flow i (D.decode.symm tagged) := by
      simpa only [Equiv.symm_apply_apply] using
        D.decode.sum_comp (fun tagged => weight tagged * f.flow i (D.decode.symm tagged))
    _ = ∑ j : Fin D.requestCount, ∑ path : D.graph.Path (D.source j) (D.target j),
        weight ⟨j, path⟩ * f.flow i (D.encode j path) := by
      rw [Fintype.sum_sigma]
      rfl
    _ = _ := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        apply Finset.sum_eq_zero
        intro path hp
        have hfalse : D.toInstance.allowed i (D.encode j path) = false := by
          simp [hji]
        rw [hf.2.2.1 i _ hfalse, mul_zero]
      · intro hi
        exact (hi (Finset.mem_univ _)).elim

theorem typed_flow_unit (D : GraphData) (f : D.toInstance.FractionalSolution)
    (hf : D.toInstance.Feasible f) (i : Fin D.requestCount) :
    (∑ path : D.graph.Path (D.source i) (D.target i), f.flow i (D.encode i path)) = 1 := by
  have hsum := weighted_request_sum D f hf i (fun _ => 1)
  simpa only [one_mul, hf.2.2.2.1 i] using hsum.symm

theorem typed_resourceFlow (D : GraphData) (f : D.toInstance.FractionalSolution)
    (hf : D.toInstance.Feasible f) (i : Fin D.requestCount) (a : Fin D.resourceCount) :
    (∑ path : D.graph.Path (D.source i) (D.target i),
      if a ∈ D.pathResources ⟨i, path⟩ then f.flow i (D.encode i path) else 0) =
      D.toInstance.resourceFlow f i a := by
  classical
  have hsum := weighted_request_sum D f hf i
    (fun tagged => if a ∈ D.pathResources tagged then 1 else 0)
  simpa [Instance.resourceFlow] using hsum.symm

end BuyAtBulk.NodeReduction
