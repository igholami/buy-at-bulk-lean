import BuyAtBulk.Computation.Runtime.SparseResource
import BuyAtBulk.Computation.StoredOriginal.Input

/-! Flattening actual sparse path families into the stored input format,
with exact re-selection and preservation of original LP constraints. -/
namespace BuyAtBulk.Computation.Runtime.SparseSupplied
open StoredOriginal CompactFlow
variable {V : Type} {G : SimpleGraph V} {h : ℕ} (source target : Fin h → V)

 def flattenFamily (paths : ∀ i, FlowDecomposition.WeightedPaths G (source i) (target i)) :
    List (Entry (G:=G) source target) :=
  (List.finRange h).flatMap fun i => (paths i).map fun e => ⟨i,e⟩

 theorem select_tagged (paths : ∀ i, FlowDecomposition.WeightedPaths G (source i) (target i))
    (j i : Fin h) :
    selectPaths source target ((paths j).map fun e => ⟨j,e⟩) i =
      if same : j=i then same ▸ paths j else [] := by
  by_cases same : j=i
  · subst j
    simp [selectPaths]
  · simp [selectPaths,List.filterMap_map,same,Function.comp_def]

 theorem select_flatten_list (paths : ∀ i, FlowDecomposition.WeightedPaths G (source i) (target i))
    (indices : List (Fin h)) (nodup : indices.Nodup) (i : Fin h) :
    selectPaths source target (indices.flatMap fun j => (paths j).map fun e => ⟨j,e⟩) i =
      if i ∈ indices then paths i else [] := by
  induction indices with
  | nil => simp [selectPaths]
  | cons j rest ih =>
    have hn := List.nodup_cons.mp nodup
    simp only [List.flatMap_cons,selectPaths,List.filterMap_append]
    change selectPaths source target ((paths j).map fun e => ⟨j,e⟩) i ++
      selectPaths source target (rest.flatMap fun j => (paths j).map fun e => ⟨j,e⟩) i = _
    rw [select_tagged,ih hn.2]
    by_cases same : j=i
    · subst j; simp [hn.1]
    · simp [same,Ne.symm same]

 @[simp] theorem select_flattenFamily
    (paths : ∀ i, FlowDecomposition.WeightedPaths G (source i) (target i)) (i : Fin h) :
    selectPaths source target (flattenFamily source target paths) i = paths i := by
  simpa [flattenFamily] using select_flatten_list source target paths (List.finRange h)
    (List.nodup_finRange h) i

 theorem flattenFamily_nonneg
    (paths : ∀ i, FlowDecomposition.WeightedPaths G (source i) (target i))
    (nonneg : ∀ i e, e ∈ paths i → 0 ≤ e.1) :
    ∀ e ∈ flattenFamily source target paths, 0 ≤ e.2.1 := by
  intro e mem
  obtain ⟨i,_,mem⟩ := List.mem_flatMap.mp mem
  obtain ⟨p,member,rfl⟩ := List.mem_map.mp mem
  exact nonneg i p member

 theorem flattenFamily_length
    (paths : ∀ i, FlowDecomposition.WeightedPaths G (source i) (target i))
    (bound : ℕ) (sparse : ∀ i, (paths i).length ≤ bound) :
    (flattenFamily source target paths).length ≤ h*bound := by
  have aux (indices : List (Fin h)) :
      (indices.flatMap fun i => (paths i).map fun e => (⟨i,e⟩ : Entry (G:=G) source target)).length ≤ indices.length*bound := by
    induction indices with
    | nil => simp
    | cons i rest ih =>
      simp only [List.flatMap_cons,List.length_append,List.length_map,List.length_cons]
      have hi := sparse i
      nlinarith
  simpa [flattenFamily] using aux (List.finRange h)

section Stored
variable {n resources : ℕ} (tables : Tables n resources h) (input : Fractional tables)
    (paths : ∀ i, FlowDecomposition.WeightedPaths tables.graphData.graph
      (tables.graphData.source i) (tables.graphData.target i))
    (nonneg : ∀ i e, e ∈ paths i → 0 ≤ e.1)
    (unit : ∀ i, ((paths i).map Prod.fst).sum = 1)
    (dom : ∀ i u v, ((paths i).map fun e => e.1*transportVisits e.2.val u v).sum ≤
      (((input.decode tables).paths i).map fun e => e.1*transportVisits e.2.val u v).sum)

 def storedOfFamily : Fractional tables where
  opening := input.opening
  entries := flattenFamily tables.graphData.source tables.graphData.target paths
  opening_bounds := input.opening_bounds
  nonneg := flattenFamily_nonneg _ _ paths nonneg
  unit i := by simp only [select_flattenFamily]; exact unit i
  capacity i a := by
    simp only [select_flattenFamily]
    exact (OriginalSparse.ofDominated tables.graphData (input.decode tables) paths nonneg unit dom).capacity i a

 @[simp] theorem storedOfFamily_paths (i : Fin h) :
    ((storedOfFamily tables input paths nonneg unit dom).decode tables).paths i = paths i :=
  select_flattenFamily _ _ paths i

 theorem storedOfFamily_count (sparse : ∀ i, (paths i).length ≤ n*n+1) :
    (storedOfFamily tables input paths nonneg unit dom).entries.length ≤ h*(n*n+1) :=
  flattenFamily_length _ _ paths _ sparse

 theorem storedOfFamily_decode :
    (storedOfFamily tables input paths nonneg unit dom).decode tables =
      OriginalSparse.ofDominated tables.graphData (input.decode tables) paths nonneg unit dom := by
  cases input
  simp only [Fractional.decode, storedOfFamily, OriginalSparse.ofDominated]
  congr
  funext i
  exact select_flattenFamily _ _ paths i

 theorem storedOfFamily_buying :
    OriginalPipeline.buyingBudget tables.graphData
      ((storedOfFamily tables input paths nonneg unit dom).decode tables) =
      OriginalPipeline.buyingBudget tables.graphData (input.decode tables) := rfl

 theorem storedOfFamily_length (i : Fin h) :
    OriginalPipeline.fractionalLength tables.graphData
      ((storedOfFamily tables input paths nonneg unit dom).decode tables) i ≤
      OriginalPipeline.fractionalLength tables.graphData (input.decode tables) i := by
  rw [storedOfFamily_decode]
  exact OriginalSparse.length_le tables.graphData (input.decode tables) paths nonneg unit dom i

 theorem storedOfFamily_rental :
    OriginalPipeline.rentalBudget tables.graphData
      ((storedOfFamily tables input paths nonneg unit dom).decode tables) ≤
      OriginalPipeline.rentalBudget tables.graphData (input.decode tables) := by
  rw [storedOfFamily_decode]
  exact OriginalSparse.rental_le tables.graphData (input.decode tables) paths nonneg unit dom

end Stored
end BuyAtBulk.Computation.Runtime.SparseSupplied
