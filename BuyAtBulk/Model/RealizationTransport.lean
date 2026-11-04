import BuyAtBulk.Model.GraphInstance
import BuyAtBulk.Model.NodeReduction.Transport
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-! Transfer an arbitrary graph-realized incidence LP to the canonical complete
simple-path presentation. Maps are per commodity; no unique-tag assumption is
made about the original path codes. Illegal codes have zero flow. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.RealizationTransport

variable (I : Instance) (realization : I.GraphRealization)

abbrev graphData : GraphData where
  Vertex := realization.Vertex
  vertexFintype := realization.vertexFintype
  graph := realization.graph
  resourceCount := I.resourceCount
  requestCount := I.requestCount
  source := realization.source
  target := realization.target
  location := realization.location
  location_injective := realization.location_injective
  location_valid := realization.location_valid
  buying := I.buying
  length := I.length
  demand := I.demand
  buying_nonneg := I.buying_nonneg
  length_nonneg := I.length_nonneg
  demand_pos := I.demand_pos

instance realizationTransportLocalInst1 : Fintype realization.Vertex := realization.vertexFintype
local instance realizationTransportLocalInst2 : DecidableEq realization.Vertex := Classical.decEq _
local instance realizationTransportLocalInst3 : DecidableRel realization.graph.Adj := Classical.decRel _

/-- Select only a witness of the actual graph-realization soundness condition. -/
def soundPath (i : Fin I.requestCount) (p : Fin I.pathCount) (allowed : I.allowed i p = true) :
    realization.graph.Path (realization.source i) (realization.target i) :=
  ⟨Classical.choose (realization.path_sound i p allowed),
    .mk' (Classical.choose_spec (realization.path_sound i p allowed)).1⟩

theorem soundPath_uses (i : Fin I.requestCount) (p : Fin I.pathCount) (allowed : I.allowed i p = true) :
    (graphData I realization).pathResources ⟨i, soundPath I realization i p allowed⟩ = I.uses p := by
  rw [(Classical.choose_spec (realization.path_sound i p allowed)).2]
  classical
  ext a
  simp only [GraphData.pathResources, Instance.walkResources, soundPath, Finset.mem_filter,
    Finset.mem_univ, true_and]
  cases ha : realization.location a <;> simp_all

theorem positive_allowed_path (f : I.FractionalSolution) (feasible : I.Feasible f) (i : Fin I.requestCount) :
    ∃ p, I.allowed i p = true ∧ 0 < f.flow i p := by
  classical
  have exists_positive : ∃ p, 0 < f.flow i p := by
    by_contra hn
    push Not at hn
    have zero : ∀ p, f.flow i p = 0 := fun p => le_antisymm (hn p) (feasible.2.1 i p)
    have unit := feasible.2.2.2.1 i
    simp [zero] at unit
  obtain ⟨p, hp⟩ := exists_positive
  refine ⟨p, ?_, hp⟩
  cases ha : I.allowed i p with
  | true => rfl
  | false => exact False.elim ((ne_of_gt hp) (feasible.2.2.1 i p ha))

def defaultPath (f : I.FractionalSolution) (feasible : I.Feasible f) (i : Fin I.requestCount) :
    realization.graph.Path (realization.source i) (realization.target i) :=
  soundPath I realization i (Classical.choose (positive_allowed_path I f feasible i))
    (Classical.choose_spec (positive_allowed_path I f feasible i)).1

def mapCode (f : I.FractionalSolution) (feasible : I.Feasible f)
    (i : Fin I.requestCount) (p : Fin I.pathCount) : Fin (graphData I realization).toInstance.pathCount := by
  classical
  exact (graphData I realization).encode i
    (if allowed : I.allowed i p = true then soundPath I realization i p allowed
      else defaultPath I realization f feasible i)

theorem mapCode_allowed (f : I.FractionalSolution) (feasible : I.Feasible f)
    (i : Fin I.requestCount) (p : Fin I.pathCount) :
    (graphData I realization).toInstance.allowed i (mapCode I realization f feasible i p) = true := by
  classical
  exact (graphData I realization).allowed_encode i _

theorem mapCode_uses (f : I.FractionalSolution) (feasible : I.Feasible f)
    (i : Fin I.requestCount) (p : Fin I.pathCount) (allowed : I.allowed i p = true) :
    (graphData I realization).toInstance.uses (mapCode I realization f feasible i p) = I.uses p := by
  classical
  simp only [mapCode, dif_pos allowed]
  rw [GraphData.decode_encode]
  exact soundPath_uses I realization i p allowed

def canonicalSolution (f : I.FractionalSolution) (feasible : I.Feasible f) :
    (graphData I realization).toInstance.FractionalSolution where
  opening := f.opening
  flow i := NodeReduction.pushflow (mapCode I realization f feasible i) (f.flow i)

theorem canonical_resourceFlow (f : I.FractionalSolution) (feasible : I.Feasible f)
    (i : Fin I.requestCount) (a : Fin I.resourceCount) :
    (graphData I realization).toInstance.resourceFlow (canonicalSolution I realization f feasible) i a =
      I.resourceFlow f i a := by
  classical
  let D := graphData I realization
  have weighted := NodeReduction.weighted_pushflow (mapCode I realization f feasible i) (f.flow i)
    (fun q => if a ∈ D.toInstance.uses q then (1 : ℚ) else 0)
  have equality : (∑ p, (if a ∈ D.toInstance.uses (mapCode I realization f feasible i p) then (1 : ℚ) else 0) * f.flow i p) =
      I.resourceFlow f i a := by
    apply Finset.sum_congr rfl
    intro p _
    cases allowed : I.allowed i p with
    | false => simp [feasible.2.2.1 i p allowed]
    | true =>
      rw [mapCode_uses I realization f feasible i p allowed]
      split_ifs <;> simp
  have hw := weighted.trans equality
  simpa only [Instance.resourceFlow, canonicalSolution, ite_mul, one_mul, zero_mul] using hw

theorem canonical_feasible (f : I.FractionalSolution) (feasible : I.Feasible f) :
    (graphData I realization).toInstance.Feasible (canonicalSolution I realization f feasible) := by
  classical
  refine ⟨feasible.1, ?_, ?_, ?_, ?_⟩
  · intro i q
    change 0 ≤ ∑ p, if mapCode I realization f feasible i p = q then f.flow i p else 0
    apply Finset.sum_nonneg
    intro p _
    split_ifs
    · exact feasible.2.1 i p
    · exact le_rfl
  · intro i q illegal
    change (∑ p, if mapCode I realization f feasible i p = q then f.flow i p else 0) = 0
    apply Finset.sum_eq_zero
    intro p _
    split_ifs with same
    · have legal := mapCode_allowed I realization f feasible i p
      rw [same, illegal] at legal
      contradiction
    · rfl
  · intro i
    have weighted := NodeReduction.weighted_pushflow (mapCode I realization f feasible i) (f.flow i) (fun _ => (1 : ℚ))
    simpa only [one_mul, feasible.2.2.2.1 i, canonicalSolution] using weighted
  · intro i a
    rw [canonical_resourceFlow I realization f feasible]
    exact feasible.2.2.2.2 i a

@[simp] theorem canonical_buyingCost (f : I.FractionalSolution) (feasible : I.Feasible f) :
    (graphData I realization).toInstance.buyingCost (canonicalSolution I realization f feasible) = I.buyingCost f := rfl

theorem canonical_fractionalLength (f : I.FractionalSolution) (feasible : I.Feasible f) (i : Fin I.requestCount) :
    (graphData I realization).toInstance.fractionalLength (canonicalSolution I realization f feasible) i = I.fractionalLength f i := by
  classical
  have weighted := NodeReduction.weighted_pushflow (mapCode I realization f feasible i) (f.flow i)
    ((graphData I realization).toInstance.pathLength)
  apply weighted.trans
  apply Finset.sum_congr rfl
  intro p _
  cases allowed : I.allowed i p with
  | false => simp [feasible.2.2.1 i p allowed]
  | true =>
    have uses := mapCode_uses I realization f feasible i p allowed
    change (graphData I realization).pathResources ((graphData I realization).decode (mapCode I realization f feasible i p)) = I.uses p at uses
    simp only [Instance.pathLength]
    rw [uses]

@[simp] theorem canonical_rentalCost (f : I.FractionalSolution) (feasible : I.Feasible f) :
    (graphData I realization).toInstance.rentalCost (canonicalSolution I realization f feasible) = I.rentalCost f := by
  apply Finset.sum_congr rfl
  intro i _
  rw [canonical_fractionalLength]

/-- Each canonical graph routing projects to an allowed original routing
using path completeness, retaining every resource occurrence and both budgets. -/
theorem project_routing (routing : (graphData I realization).toInstance.IntegralRouting) :
    ∃ original : I.IntegralRouting,
      I.usedResources original = (graphData I realization).toInstance.usedResources routing ∧
      I.integralBuyingCost original = (graphData I realization).toInstance.integralBuyingCost routing ∧
      I.integralRentalCost original = (graphData I realization).toInstance.integralRentalCost routing := by
  classical
  let D := graphData I realization
  have per_request : ∀ i, ∃ p : Fin I.pathCount, I.allowed i p = true ∧ I.uses p = D.toInstance.uses (routing.path i) := by
    intro i
    obtain ⟨walk, simple, resource⟩ := D.realization.path_sound i (routing.path i) (routing.allowed_path i)
    obtain ⟨p, allowed, uses⟩ := realization.path_complete i walk simple
    refine ⟨p, allowed, ?_⟩
    rw [uses, resource]
    rfl
  let original : I.IntegralRouting := {
    path := fun i => Classical.choose (per_request i)
    allowed_path := fun i => (Classical.choose_spec (per_request i)).1 }
  have uses : ∀ i, I.uses (original.path i) = D.toInstance.uses (routing.path i) :=
    fun i => (Classical.choose_spec (per_request i)).2
  have union : I.usedResources original = D.toInstance.usedResources routing := by
    unfold Instance.usedResources
    apply Finset.biUnion_congr rfl
    intro i _
    exact uses i
  refine ⟨original, union, ?_, ?_⟩
  · unfold Instance.integralBuyingCost
    rw [union]
  · apply Finset.sum_congr rfl
    intro i _
    have lengths : I.pathLength (original.path i) = D.toInstance.pathLength (routing.path i) := by
      unfold Instance.pathLength
      rw [uses]
    rw [lengths]

end BuyAtBulk.RealizationTransport
