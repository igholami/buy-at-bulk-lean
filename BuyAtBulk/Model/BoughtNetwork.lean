import BuyAtBulk.Model.GraphRealization
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Bought resource sets and actual shortest physical distances. A path is
available exactly when all of its priced node/edge resources have been bought;
unassigned nodes and edges remain free. Distances are only evaluated after
connectivity has been proved, so disconnected pairs never receive value zero. -/
noncomputable section
namespace BuyAtBulk.Instance

variable (I : BuyAtBulk.Instance) (realization : I.GraphRealization)
local instance boughtNetworkFintype : Fintype realization.Vertex := realization.vertexFintype
local instance boughtNetworkDecEq : DecidableEq realization.Vertex := Classical.decEq _
local instance boughtNetworkAdj : DecidableRel realization.graph.Adj := Classical.decRel _

/-- The source's bought network, represented by purchased resources. All
original terminal pairs must have an actual available simple graph path. -/
structure BoughtNetwork where
  resources : Finset (Fin I.resourceCount)
  connected : ∀ i, ∃ path : realization.graph.Path (realization.source i) (realization.target i),
    I.walkResources realization.location path.val ⊆ resources

namespace BoughtNetwork
variable {I realization} (network : I.BoughtNetwork realization)

def available (i : Fin I.requestCount) :
    Finset (realization.graph.Path (realization.source i) (realization.target i)) :=
  Finset.univ.filter fun path => I.walkResources realization.location path.val ⊆ network.resources

def physicalLength (_network : I.BoughtNetwork realization) {u v : realization.Vertex} (walk : realization.graph.Walk u v) : ℚ :=
  ∑ a ∈ I.walkResources realization.location walk, I.length a

theorem available_nonempty (i : Fin I.requestCount) : (network.available i).Nonempty := by
  obtain ⟨path, supported⟩ := network.connected i
  exact ⟨path, Finset.mem_filter.mpr ⟨Finset.mem_univ _, supported⟩⟩

/-- The actual shortest physical length in the bought network, including
node lengths at both endpoints and all priced traversed edges. -/
def distance (i : Fin I.requestCount) : ℚ :=
  ((network.available i).image fun path => network.physicalLength path.val).min'
    ((network.available_nonempty i).image _)

def buyingCost : ℚ := ∑ a ∈ network.resources, I.buying a

def rentalCost : ℚ := ∑ i, I.demand i * network.distance i

theorem distance_le_path (i : Fin I.requestCount)
    (path : realization.graph.Path (realization.source i) (realization.target i))
    (supported : I.walkResources realization.location path.val ⊆ network.resources) :
    network.distance i ≤ network.physicalLength path.val := by
  exact Finset.min'_le _ _ (Finset.mem_image.mpr
    ⟨path, Finset.mem_filter.mpr ⟨Finset.mem_univ _, supported⟩, rfl⟩)

theorem exists_shortest (i : Fin I.requestCount) :
    ∃ path : realization.graph.Path (realization.source i) (realization.target i),
      I.walkResources realization.location path.val ⊆ network.resources ∧
      network.physicalLength path.val = network.distance i := by
  have member := Finset.min'_mem
    ((network.available i).image fun path => network.physicalLength path.val)
    ((network.available_nonempty i).image _)
  obtain ⟨path, available, length⟩ := Finset.mem_image.mp member
  exact ⟨path, (Finset.mem_filter.mp available).2, length⟩

theorem distance_nonneg (i : Fin I.requestCount) : 0 ≤ network.distance i := by
  obtain ⟨path, _, length⟩ := network.exists_shortest i
  rw [← length]
  exact Finset.sum_nonneg fun a _ => I.length_nonneg a

end BoughtNetwork

/-- Reconstruct the source bought network from an incidence routing. -/
def IntegralRouting.toBoughtNetwork (routing : I.IntegralRouting) : I.BoughtNetwork realization where
  resources := I.usedResources routing
  connected i := by
    obtain ⟨walk, simple, uses⟩ := realization.path_sound i (routing.path i) (routing.allowed_path i)
    refine ⟨⟨walk, .mk' simple⟩, ?_⟩
    rw [← uses]
    exact Finset.subset_biUnion_of_mem (fun i => I.uses (routing.path i)) (Finset.mem_univ i)

@[simp] theorem IntegralRouting.toBoughtNetwork_buying (routing : I.IntegralRouting) :
    (routing.toBoughtNetwork I realization).buyingCost = I.integralBuyingCost routing := rfl

theorem IntegralRouting.toBoughtNetwork_rental (routing : I.IntegralRouting) :
    (routing.toBoughtNetwork I realization).rentalCost ≤ I.integralRentalCost routing := by
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (I.demand_pos i).le
  obtain ⟨walk, simple, uses⟩ := realization.path_sound i (routing.path i) (routing.allowed_path i)
  have supported : I.walkResources realization.location walk ⊆ I.usedResources routing := by
    rw [← uses]
    exact Finset.subset_biUnion_of_mem (fun i => I.uses (routing.path i)) (Finset.mem_univ i)
  have shortest := (routing.toBoughtNetwork I realization).distance_le_path i ⟨walk, .mk' simple⟩ supported
  simpa only [BoughtNetwork.physicalLength, Instance.pathLength, uses] using shortest

end BuyAtBulk.Instance
