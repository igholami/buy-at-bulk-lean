import BuyAtBulk.Computation.Runtime.OriginalSized

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.Computation.Runtime.Original
open BuyAtBulk.NodeReduction BuyAtBulk.Computation.StoredOriginal
open scoped BuyAtBulk.Computation.NodeReduction
variable {n resources requests : ℕ} (tables : Tables n resources requests)

def numberSized (vertices : List (Vertex tables.graphData)) (same : vertices=modelVertices tables)
    (m : ℕ) (size : m=vertices.length) (vertex : Vertex tables.graphData) : Traced (Fin m) :=
  let found := position tables vertex vertices
  let index : Fin m := ⟨found.value,by
    rw [size,position_value,same]
    exact List.idxOf_lt_length_iff.mpr
      (BuyAtBulk.Computation.NodeReduction.vertexList_complete tables.graphData (Equiv.refl _) vertex)⟩
  ⟨index,found.events++[⟨.write,[found.value.size]⟩]⟩

@[simp] theorem numberSized_value (vertices : List (Vertex tables.graphData)) (same : vertices=modelVertices tables)
    (m : ℕ) (size : m=vertices.length) (vertex : Vertex tables.graphData) :
    (numberSized tables vertices same m size vertex).value=sizedNumbering tables vertices same m size vertex := by
  subst vertices
  subst m
  exact numberVertex_value tables (modelVertices tables) rfl vertex

theorem numberSized_count (vertices : List (Vertex tables.graphData)) (same : vertices=modelVertices tables)
    (m : ℕ) (size : m=vertices.length) (vertex : Vertex tables.graphData) :
    (numberSized tables vertices same m size vertex).events.length ≤ 27*m+3 := by
  have count := position_count tables vertex vertices
  simp only [numberSized,List.length_append,List.length_cons,List.length_nil]
  omega

theorem numberSized_words (vertices : List (Vertex tables.graphData)) (same : vertices=modelVertices tables)
    (m : ℕ) (size : m=vertices.length) (vertex : Vertex tables.graphData)
    (K : ℕ) (dimension : n+requests+m+3 ≤ K) :
    WordsWithin K (numberSized tables vertices same m size vertex).events := by
  have lookup := position_words tables vertex vertices K (by simpa only [size] using dimension)
  have length : (position tables vertex vertices).value ≤ m := by
    have bound := List.idxOf_le_length (a:=vertex) (l:=vertices)
    simpa only [←position_value,size] using bound
  have index : (position tables vertex vertices).value.size ≤ K :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  simp_all [numberSized,wordsWithin_append,wordsWithin_cons]

def sizedEndpoints (vertices : List (Vertex tables.graphData)) (same : vertices=modelVertices tables)
    (m : ℕ) (size : m=vertices.length) (side : Bool) : Traced (Vector (Fin m) requests) :=
  Weights.materialize (fun i=>numberSized tables vertices same m size (.leaf i side)) (fun i=>i.val.size)
@[simp] theorem sizedEndpoints_value (vertices : List (Vertex tables.graphData)) (same : vertices=modelVertices tables)
    (m : ℕ) (size : m=vertices.length) (side : Bool) (i : Fin requests) :
    (sizedEndpoints tables vertices same m size side).value[i.val]=sizedNumbering tables vertices same m size (.leaf i side) := by
  simp only [sizedEndpoints,Weights.materialize_get,numberSized_value]

theorem sizedEndpoints_count (vertices : List (Vertex tables.graphData)) (same : vertices=modelVertices tables)
    (m : ℕ) (size : m=vertices.length) (side : Bool) :
    (sizedEndpoints tables vertices same m size side).events.length ≤ requests*(27*m+5)+1 :=
  Weights.materialize_count _ _ _ (by intro i;exact numberSized_count tables vertices same m size _)

theorem sizedEndpoints_words (vertices : List (Vertex tables.graphData)) (same : vertices=modelVertices tables)
    (m : ℕ) (size : m=vertices.length) (side : Bool) (K : ℕ) (dimension : n+requests+m+3 ≤ K) :
    WordsWithin K (sizedEndpoints tables vertices same m size side).events := by
  apply Weights.materialize_words
  · omega
  · exact fun i=>numberSized_words tables vertices same m size (.leaf i side) K dimension
  · intro i
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by
      have := (numberSized tables vertices same m size (.leaf i side)).value.isLt
      omega)

end BuyAtBulk.Computation.Runtime.Original
