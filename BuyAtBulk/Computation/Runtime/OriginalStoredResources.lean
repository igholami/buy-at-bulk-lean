import BuyAtBulk.Computation.Runtime.OriginalCached

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.Computation.Runtime.Original
open BuyAtBulk.NodeReduction BuyAtBulk.Computation.StoredOriginal
open scoped BuyAtBulk.Computation.NodeReduction
variable {n resources requests : ℕ} (tables : Tables n resources requests)
variable (prepared : CachedBuffers tables)

def storedBoughtCell (bought : Vector Bool prepared.count) (a : Fin resources) : Traced Bool :=
  let vertex := resourceVertex tables.graphData a
  let index := numberSized tables prepared.vertices prepared.complete prepared.count prepared.size vertex
  ⟨bought[index.value.val],[⟨Operation.read,[a.val.size,n.size,n.size]⟩,⟨.branch,[1]⟩]++index.events++
    [⟨.read,[index.value.val.size,1]⟩,⟨.write,[a.val.size,1]⟩]⟩
@[simp] theorem storedBoughtCell_value (bought : Vector Bool prepared.count) (a : Fin resources) :
    (storedBoughtCell tables prepared bought a).value=
      bought[(sizedNumbering tables prepared.vertices prepared.complete prepared.count prepared.size
        (resourceVertex tables.graphData a)).val] := by
  simp only [storedBoughtCell,numberSized_value]
theorem storedBoughtCell_count (bought : Vector Bool prepared.count) (a : Fin resources) :
    (storedBoughtCell tables prepared bought a).events.length ≤ 27*prepared.count+7 := by
  have count := numberSized_count tables prepared.vertices prepared.complete prepared.count prepared.size (resourceVertex tables.graphData a)
  simp only [storedBoughtCell,List.length_append,List.length_cons,List.length_nil]
  omega

def storedBoughtResources (bought : Vector Bool prepared.count) : Traced (Vector Bool resources) :=
  Weights.materialize (storedBoughtCell tables prepared bought) (fun _=>1)
@[simp] theorem storedBoughtResources_value (bought : Vector Bool prepared.count) (a : Fin resources) :
    (storedBoughtResources tables prepared bought).value[a.val]=
      bought[(sizedNumbering tables prepared.vertices prepared.complete prepared.count prepared.size
        (resourceVertex tables.graphData a)).val] := by
  simp only [storedBoughtResources,Weights.materialize_get,storedBoughtCell_value]
theorem storedBoughtResources_count (bought : Vector Bool prepared.count) :
    (storedBoughtResources tables prepared bought).events.length ≤ resources*(27*prepared.count+9)+1 :=
  Weights.materialize_count _ _ _ (storedBoughtCell_count tables prepared bought)

theorem storedBoughtCell_words (bought : Vector Bool prepared.count) (a : Fin resources) (K : ℕ)
    (dimension : n+resources+requests+prepared.count+3 ≤ K) :
    WordsWithin K (storedBoughtCell tables prepared bought a).events := by
  have lookup := numberSized_words tables prepared.vertices prepared.complete prepared.count prepared.size
    (resourceVertex tables.graphData a) K (by omega)
  have ai : a.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := a.isLt;omega)
  have ni : n.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have index : (numberSized tables prepared.vertices prepared.complete prepared.count prepared.size
      (resourceVertex tables.graphData a)).value.val.size ≤ K :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by
      have := (numberSized tables prepared.vertices prepared.complete prepared.count prepared.size
        (resourceVertex tables.graphData a)).value.isLt
      omega)
  have one : 1 ≤ K := by omega
  simp_all [storedBoughtCell,wordsWithin_append,wordsWithin_cons]

theorem storedBoughtResources_words (bought : Vector Bool prepared.count) (K : ℕ)
    (dimension : n+resources+requests+prepared.count+3 ≤ K) :
    WordsWithin K (storedBoughtResources tables prepared bought).events := by
  apply Weights.materialize_words
  · omega
  · exact fun a=>storedBoughtCell_words tables prepared bought a K dimension
  · intro a;omega

theorem storedBoughtResources_cost (computed : prepared=(cachedBuffers tables).value)
    (bought : Vector Bool prepared.count) :
    (∑ a : Fin resources,if (storedBoughtResources tables prepared bought).value[a.val] then tables.buying[a.val] else 0)=
      ∑ v : Fin prepared.count,if bought[v.val] then prepared.buying[v.val] else 0 := by
  classical
  have buying (v : Fin prepared.count) : prepared.buying[v.val]=OriginalPipeline.resourceCost tables.graphData
      (fun a=>tables.buying[a.val]) ((sizedNumbering tables prepared.vertices prepared.complete prepared.count prepared.size).symm v) := by
    cases computed
    exact cachedBuffers_buying tables v
  simp only [storedBoughtResources_value,buying,OriginalPipeline.resourceCost]
  symm
  calc
    _ = ∑ v : Fin prepared.count,∑ a : Fin resources,
        if resourceVertex tables.graphData a=(sizedNumbering tables prepared.vertices prepared.complete prepared.count prepared.size).symm v then
          (if bought[v.val] then tables.buying[a.val] else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      cases flag : bought[v.val] <;> simp [flag]
    _ = ∑ a : Fin resources,∑ v : Fin prepared.count,
        if resourceVertex tables.graphData a=(sizedNumbering tables prepared.vertices prepared.complete prepared.count prepared.size).symm v then
          (if bought[v.val] then tables.buying[a.val] else 0) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      have eq (v : Fin prepared.count) :
          resourceVertex tables.graphData a=(sizedNumbering tables prepared.vertices prepared.complete prepared.count prepared.size).symm v ↔
            v=sizedNumbering tables prepared.vertices prepared.complete prepared.count prepared.size (resourceVertex tables.graphData a) := by
        constructor
        · intro same
          have mapped := congrArg (sizedNumbering tables prepared.vertices prepared.complete prepared.count prepared.size) same
          simpa using mapped.symm
        · intro same
          subst v
          simp
      simp_rw [eq]
      simp

end BuyAtBulk.Computation.Runtime.Original
