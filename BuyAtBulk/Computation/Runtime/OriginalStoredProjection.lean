import BuyAtBulk.Computation.Runtime.OriginalCached
import BuyAtBulk.Computation.Runtime.OriginalSizedProjection

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.Computation.Runtime.Original
open BuyAtBulk.NodeReduction BuyAtBulk.Computation.StoredOriginal
open scoped BuyAtBulk.Computation.NodeReduction
variable {n resources requests : ℕ} (tables : Tables n resources requests)

def retypeStored {V : Type} {G H : SimpleGraph V} {s t s' t' : V}
    (graphs : G=H) (source : s=s') (target : t=t') (path : G.Path s t) : H.Path s' t' := by
  subst H
  exact ShortestPath.copyPath path source target

theorem retypeStored_length {V : Type} {G H : SimpleGraph V} {s t s' t' : V}
    (graphs : G=H) (source : s=s') (target : t=t') (path : G.Path s t) :
    (retypeStored graphs source target path).val.length=path.val.length := by
  subst H
  simp only [retypeStored,ShortestPath.copyPath,SimpleGraph.Walk.length_copy]

theorem retypeStored_support {V : Type} {G H : SimpleGraph V} {s t s' t' : V}
    (graphs : G=H) (source : s=s') (target : t=t') (path : G.Path s t) :
    (retypeStored graphs source target path).val.support=path.val.support := by
  subst H
  simp only [retypeStored,ShortestPath.copyPath,SimpleGraph.Walk.support_copy]

theorem retypeStored_weight {V : Type} [Fintype V] {G H : SimpleGraph V} {s t s' t' : V}
    (graphs : G=H) (source : s=s') (target : t=t') (path : G.Path s t) (weight : V→ℚ) :
    NodeMetric.walkWeight H weight (retypeStored graphs source target path).val=
      NodeMetric.walkWeight G weight path.val := by
  subst H
  exact ShortestPath.copyPath_weight weight path source target

section Prepared
variable (prepared : CachedBuffers tables) (computed : prepared=(cachedBuffers tables).value)

def storedSizedPath (i : Fin requests)
    (path : prepared.graphInput.graph.Path prepared.source[i.val] prepared.target[i.val]) :
    (sizedGraph tables prepared.vertices prepared.count prepared.size).value.graph.Path
      (sizedNumbering tables prepared.vertices prepared.complete prepared.count prepared.size (.leaf i false))
      (sizedNumbering tables prepared.vertices prepared.complete prepared.count prepared.size (.leaf i true)) :=
  retypeStored (by cases computed;rfl)
    (by cases computed;exact cachedBuffers_source tables i)
    (by cases computed;exact cachedBuffers_target tables i) path

theorem storedSizedPath_length (i : Fin requests)
    (path : prepared.graphInput.graph.Path prepared.source[i.val] prepared.target[i.val]) :
    (storedSizedPath tables prepared computed i path).val.length=path.val.length :=
  retypeStored_length _ _ _ _

theorem storedSizedPath_support (i : Fin requests)
    (path : prepared.graphInput.graph.Path prepared.source[i.val] prepared.target[i.val]) :
    (storedSizedPath tables prepared computed i path).val.support=path.val.support :=
  retypeStored_support _ _ _ _

def projectStoredPath (i : Fin requests)
    (path : prepared.graphInput.graph.Path prepared.source[i.val] prepared.target[i.val]) :
    Traced (tables.graphData.graph.Path (tables.graphData.source i) (tables.graphData.target i)) :=
  projectSized tables prepared.vertices prepared.complete prepared.count prepared.size i
    (storedSizedPath tables prepared computed i path)

theorem projectStoredPath_count (i : Fin requests)
    (path : prepared.graphInput.graph.Path prepared.source[i.val] prepared.target[i.val]) :
    (projectStoredPath tables prepared computed i path).events.length ≤
      (14*(prepared.count+1)+17)*(path.val.length+1)+10 := by
  have result := projectSized_count tables prepared.vertices prepared.complete prepared.count prepared.size i
    (storedSizedPath tables prepared computed i path)
  simpa only [projectStoredPath,storedSizedPath_length] using result

theorem projectStoredPath_words (i : Fin requests)
    (path : prepared.graphInput.graph.Path prepared.source[i.val] prepared.target[i.val])
    (K : ℕ) (dimension : n+requests+prepared.count+6 ≤ K) :
    WordsWithin K (projectStoredPath tables prepared computed i path).events :=
  projectSized_words tables prepared.vertices prepared.complete prepared.count prepared.size i
    (storedSizedPath tables prepared computed i path) K dimension

theorem projectStoredPath_resource_iff (i : Fin requests)
    (path : prepared.graphInput.graph.Path prepared.source[i.val] prepared.target[i.val]) (a : Fin resources) :
    OriginalPipeline.usesResource tables.graphData i (projectStoredPath tables prepared computed i path).value a=true ↔
      sizedNumbering tables prepared.vertices prepared.complete prepared.count prepared.size
        (resourceVertex tables.graphData a)∈path.val.support := by
  have result := projectSized_resource_iff tables prepared.vertices prepared.complete prepared.count prepared.size i
    (storedSizedPath tables prepared computed i path) a
  simpa only [projectStoredPath,storedSizedPath_support] using result

theorem projectStoredPath_rental (i : Fin requests)
    (path : prepared.graphInput.graph.Path prepared.source[i.val] prepared.target[i.val]) :
    OriginalPipeline.pathResourceCost tables.graphData tables.graphData.length i
      (projectStoredPath tables prepared computed i path).value=
        NodeMetric.walkWeight prepared.graphInput.graph (fun v=>prepared.physical[v.val]) path.val := by
  rw [projectStoredPath,projectSized_resourceCost]
  have weights : (fun v=>OriginalPipeline.resourceCost tables.graphData tables.graphData.length
      ((sizedNumbering tables prepared.vertices prepared.complete prepared.count prepared.size).symm v))=
      fun v=>prepared.physical[v.val] := by
    funext v
    cases computed
    exact (cachedBuffers_physical tables v).symm
  rw [weights]
  exact retypeStored_weight _ _ _ path _

end Prepared
end BuyAtBulk.Computation.Runtime.Original
