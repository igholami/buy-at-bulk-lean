import BuyAtBulk.Model.NodeReduction.NodeLPBridge

/-! Reverse the all-vertex typed path representation by restricting openings to
paid resource nodes and pushing typed path weights to complete tagged codes. -/
noncomputable section
namespace BuyAtBulk.NodeReduction
local instance nodeLPReverseDecEq (D : GraphData) : DecidableEq (Vertex D) := Classical.decEq _
local instance nodeLPReverseDecRel (D : GraphData) : DecidableRel (graph D).Adj := Classical.decRel _

abbrev ReducedPath (D : GraphData) (i : Fin D.requestCount) :=
  (graph D).Path (.leaf i false) (.leaf i true)

def fromNodeFlow (D : GraphData) (opening : Vertex D → ℚ)
    (flow : ∀ i, ReducedPath D i → ℚ) : (reduced D).toInstance.FractionalSolution where
  opening := fun a => opening (resourceVertex D a)
  flow := fun i code => ∑ p, if (reduced D).encode i p = code then flow i p else 0

theorem fromNodeFlow_weighted (D : GraphData) (opening : Vertex D → ℚ)
    (flow : ∀ i, ReducedPath D i → ℚ) (i : Fin D.requestCount)
    (weight : Fin (reduced D).toInstance.pathCount → ℚ) :
    (∑ code, weight code * (fromNodeFlow D opening flow).flow i code) =
      ∑ p, weight ((reduced D).encode i p) * flow i p := by
  classical
  simp only [fromNodeFlow, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  simp

theorem fromNodeFlow_resourceFlow (D : GraphData) (opening : Vertex D → ℚ)
    (flow : ∀ i, ReducedPath D i → ℚ) (i : Fin D.requestCount) (a : Fin D.resourceCount) :
    (reduced D).toInstance.resourceFlow (fromNodeFlow D opening flow) i a =
      ∑ p, if resourceVertex D a ∈ p.val.support then flow i p else 0 := by
  classical
  have hw := fromNodeFlow_weighted D opening flow i
    (fun code => if a ∈ (reduced D).toInstance.uses code then 1 else 0)
  have hcode : (reduced D).toInstance.resourceFlow (fromNodeFlow D opening flow) i a =
      ∑ p, if a ∈ (reduced D).pathResources ⟨i, p⟩ then flow i p else 0 := by
    simpa only [Instance.resourceFlow, GraphData.uses_encode, GraphData.decode_encode,
      ite_mul, one_mul, zero_mul] using hw
  apply hcode.trans
  apply Finset.sum_congr rfl
  intro p _
  have hm := reduced_resource_mem D i p a
  by_cases hv : resourceVertex D a ∈ p.val.support
  · have ha := hm.mpr hv
    simp only [ite_eq_left hv, ite_eq_left ha]
  · have ha : a ∉ (reduced D).pathResources ⟨i, p⟩ := fun ha => hv (hm.mp ha)
    simp only [ite_eq_right hv, ite_eq_right ha]

theorem fromNodeFlow_feasible (D : GraphData) (opening : Vertex D → ℚ)
    (flow : ∀ i, ReducedPath D i → ℚ)
    (hopening : ∀ v, 0 ≤ opening v ∧ opening v ≤ 1)
    (hnonneg : ∀ i p, 0 ≤ flow i p) (hunit : ∀ i, ∑ p, flow i p = 1)
    (hcap : ∀ i v, (∑ p, if v ∈ p.val.support then flow i p else 0) ≤ opening v) :
    (reduced D).toInstance.Feasible (fromNodeFlow D opening flow) := by
  classical
  refine ⟨fun a => hopening _, ?_, ?_, ?_, ?_⟩
  · intro i code
    apply Finset.sum_nonneg
    intro p _
    split_ifs
    · exact hnonneg i p
    · exact le_rfl
  · intro i code hillegal
    apply Finset.sum_eq_zero
    intro p _
    split_ifs with heq
    · have htrue := (reduced D).allowed_encode i p
      rw [heq, hillegal] at htrue
      cases htrue
    · rfl
  · intro i
    have hw := fromNodeFlow_weighted D opening flow i (fun _ => 1)
    simpa [hunit] using hw
  · intro i a
    rw [fromNodeFlow_resourceFlow]
    exact hcap i (resourceVertex D a)

theorem fromNodeFlow_buyingCost (D : GraphData) (opening : Vertex D → ℚ)
    (flow : ∀ i, ReducedPath D i → ℚ) :
    (reduced D).toInstance.buyingCost (fromNodeFlow D opening flow) =
      ∑ v, nodeCost D D.buying v * opening v :=
  (nodeCost_budget D D.buying opening).symm

theorem fromNodeFlow_fractionalLength (D : GraphData) (opening : Vertex D → ℚ)
    (flow : ∀ i, ReducedPath D i → ℚ) (i : Fin D.requestCount) :
    (reduced D).toInstance.fractionalLength (fromNodeFlow D opening flow) i =
      ∑ p, NodeMetric.walkWeight (graph D) (nodeCost D D.length) p.val * flow i p := by
  have hw := fromNodeFlow_weighted D opening flow i (reduced D).toInstance.pathLength
  calc
    _ = ∑ p, (reduced D).toInstance.pathLength ((reduced D).encode i p) * flow i p := hw
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      rw [nodeCost_pathLength D i p]

theorem fromNodeFlow_rentalCost (D : GraphData) (opening : Vertex D → ℚ)
    (flow : ∀ i, ReducedPath D i → ℚ) :
    (reduced D).toInstance.rentalCost (fromNodeFlow D opening flow) =
      ∑ i, D.demand i * ∑ p,
        NodeMetric.walkWeight (graph D) (nodeCost D D.length) p.val * flow i p := by
  unfold Instance.rentalCost
  simp_rw [fromNodeFlow_fractionalLength]

end BuyAtBulk.NodeReduction
