import BuyAtBulk.Computation.Runtime.OriginalStoredProjection
import BuyAtBulk.Computation.Runtime.OriginalStoredResources

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.Computation.Runtime.Original
open BuyAtBulk.NodeReduction BuyAtBulk.Computation.StoredOriginal
open scoped BuyAtBulk.Computation.NodeReduction
variable {n resources requests : ℕ} (tables : Tables n resources requests)
variable (prepared : CachedBuffers tables) (computed : prepared=(cachedBuffers tables).value)

abbrev StoredRoute := Σ i : Fin requests,prepared.graphInput.graph.Path prepared.source[i.val] prepared.target[i.val]

def storedRoutes (routes : List (StoredRoute tables prepared)) : Traced (List tables.graphData.TaggedPath) :=
  match routes with
  | [] => ⟨[],[⟨.branch,[1]⟩]⟩
  | entry::rest =>
    let path := projectStoredPath tables prepared computed entry.1 entry.2
    let tail := storedRoutes rest
    ⟨⟨entry.1,path.value⟩::tail.value,
      [⟨.branch,[1]⟩,⟨.scan,[1]⟩,⟨.read,[entry.1.val.size]⟩]++path.events++tail.events++[⟨.cons,[entry.1.val.size]⟩]⟩

termination_by routes.length

@[simp] theorem storedRoutes_value (routes : List (StoredRoute tables prepared)) :
    (storedRoutes tables prepared computed routes).value=routes.map (fun e=>
      (⟨e.1,(projectStoredPath tables prepared computed e.1 e.2).value⟩ : tables.graphData.TaggedPath)) := by
  induction routes <;> simp_all [storedRoutes]

theorem storedRoutes_count (routes : List (StoredRoute tables prepared)) :
    (storedRoutes tables prepared computed routes).events.length ≤
      ((14*(prepared.count+1)+17)*(prepared.count+1)+14)*routes.length+1 := by
  induction routes with
  | nil => simp [storedRoutes]
  | cons entry rest ih =>
    have path := projectStoredPath_count tables prepared computed entry.1 entry.2
    have length := entry.2.property.length_lt
    simp only [Fintype.card_fin] at length
    have bound : (projectStoredPath tables prepared computed entry.1 entry.2).events.length ≤
        (14*(prepared.count+1)+17)*(prepared.count+1)+10 := by nlinarith
    simp only [storedRoutes,List.length_append,List.length_cons,List.length_nil]
    nlinarith

theorem storedRoutes_words (routes : List (StoredRoute tables prepared)) (K : ℕ)
    (dimension : n+requests+prepared.count+6 ≤ K) :
    WordsWithin K (storedRoutes tables prepared computed routes).events := by
  have one : 1 ≤ K := by omega
  induction routes with
  | nil => simp [storedRoutes,WordsWithin];omega
  | cons entry rest ih =>
    have path := projectStoredPath_words tables prepared computed entry.1 entry.2 K dimension
    have index : entry.1.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := entry.1.isLt;omega)
    simp_all [storedRoutes,wordsWithin_append,wordsWithin_cons]

structure StoredOriginalOutput where
  bought : Vector Bool resources
  routes : List tables.graphData.TaggedPath

def storedOutput (bought : Vector Bool prepared.count) (routes : List (StoredRoute tables prepared)) :
    Traced (StoredOriginalOutput tables) :=
  let paid := storedBoughtResources tables prepared bought
  let paths := storedRoutes tables prepared computed routes
  ⟨⟨paid.value,paths.value⟩,paid.events++paths.events++[⟨.cons,[resources.size]⟩]⟩

theorem storedOutput_count (bought : Vector Bool prepared.count) (routes : List (StoredRoute tables prepared)) :
    (storedOutput tables prepared computed bought routes).events.length ≤
      resources*(27*prepared.count+9)+
        ((14*(prepared.count+1)+17)*(prepared.count+1)+14)*routes.length+3 := by
  have paid := storedBoughtResources_count tables prepared bought
  have paths := storedRoutes_count tables prepared computed routes
  simp only [storedOutput,List.length_append,List.length_cons,List.length_nil]
  omega

theorem storedOutput_words (bought : Vector Bool prepared.count) (routes : List (StoredRoute tables prepared)) (K : ℕ)
    (dimension : n+resources+requests+prepared.count+6 ≤ K) :
    WordsWithin K (storedOutput tables prepared computed bought routes).events := by
  have paid := storedBoughtResources_words tables prepared bought K (by omega)
  have paths := storedRoutes_words tables prepared computed routes K (by omega)
  have ri : resources.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  simp_all [storedOutput,wordsWithin_append,wordsWithin_cons]

theorem storedOutput_supported (bought : Vector Bool prepared.count) (routes : List (StoredRoute tables prepared))
    (support : ∀ e∈routes,∀ v∈e.2.val.support,bought[v.val]=true) :
    ∀ e∈(storedOutput tables prepared computed bought routes).value.routes,∀ a,
      OriginalPipeline.usesResource tables.graphData e.1 e.2 a=true →
        (storedOutput tables prepared computed bought routes).value.bought[a.val]=true := by
  intro e member a used
  change e∈(storedRoutes tables prepared computed routes).value at member
  rw [storedRoutes_value] at member
  obtain ⟨native,native_mem,rfl⟩ := List.mem_map.mp member
  change (storedBoughtResources tables prepared bought).value[a.val]=true
  rw [storedBoughtResources_value]
  exact support native native_mem _ ((projectStoredPath_resource_iff tables prepared computed native.1 native.2 a).mp used)

theorem storedOutput_buying (bought : Vector Bool prepared.count) (routes : List (StoredRoute tables prepared)) :
    (∑ a : Fin resources,if (storedOutput tables prepared computed bought routes).value.bought[a.val]
      then tables.buying[a.val] else 0)=
      ∑ v : Fin prepared.count,if bought[v.val] then prepared.buying[v.val] else 0 :=
  storedBoughtResources_cost tables prepared computed bought

theorem storedOutput_rental (bought : Vector Bool prepared.count) (routes : List (StoredRoute tables prepared)) :
    (((storedOutput tables prepared computed bought routes).value.routes).map fun e=>
      tables.demand[e.1.val]*OriginalPipeline.pathResourceCost tables.graphData tables.graphData.length e.1 e.2).sum=
      (routes.map fun e=>prepared.demand[e.1.val]*NodeMetric.walkWeight prepared.graphInput.graph
        (fun v=>prepared.physical[v.val]) e.2.val).sum := by
  change (((storedRoutes tables prepared computed routes).value).map _).sum=_
  rw [storedRoutes_value,List.map_map]
  congr 1
  apply List.map_congr_left
  intro e _
  dsimp only [Function.comp_def]
  rw [projectStoredPath_rental]
  have demand : prepared.demand[e.1.val]=tables.demand[e.1.val] := by
    cases computed
    exact cachedBuffers_demand tables e.1
  rw [demand]

end BuyAtBulk.Computation.Runtime.Original
