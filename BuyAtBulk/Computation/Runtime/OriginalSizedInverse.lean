import BuyAtBulk.Computation.Runtime.OriginalSized
import BuyAtBulk.Computation.OriginalPipeline.Output

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.Computation.Runtime.Original
open BuyAtBulk.NodeReduction BuyAtBulk.Computation.StoredOriginal
open scoped BuyAtBulk.Computation.NodeReduction
variable {n resources requests : ℕ} (tables : Tables n resources requests)

section Inverse
variable (vertices : List (Vertex tables.graphData)) (same : vertices=modelVertices tables)
  (m : ℕ) (size : m=vertices.length)

def inverseSizedWalk {u v : Fin m} (walk : (sizedGraph tables vertices m size).value.graph.Walk u v) :
    Traced ((graph tables.graphData).Walk ((sizedNumbering tables vertices same m size).symm u)
      ((sizedNumbering tables vertices same m size).symm v)) :=
  match walk with
  | .nil =>
    let vertex := getSized tables vertices m size u
    ⟨.nil,vertex.events++[⟨.branch,[1]⟩,⟨.path,[u.val.size]⟩]⟩
  | @SimpleGraph.Walk.cons _ _ u w v edge tail =>
    let vertex := getSized tables vertices m size w
    let next := inverseSizedWalk tail
    let copied := next.value.copy (getSized_numbering tables vertices same m size w).symm rfl
    let adjacent : (graph tables.graphData).Adj ((sizedNumbering tables vertices same m size).symm u) vertex.value := by
      rw [getSized_numbering tables vertices same]
      exact (sizedIso tables vertices same m size).symm.map_rel_iff.mpr edge
    ⟨.cons adjacent copied,[⟨.branch,[1]⟩]++vertex.events++next.events++[⟨.cons,[w.val.size]⟩]⟩
termination_by walk.length

theorem inverseSizedWalk_value {u v : Fin m} (walk : (sizedGraph tables vertices m size).value.graph.Walk u v) :
    (inverseSizedWalk tables vertices same m size walk).value=walk.map (sizedIso tables vertices same m size).symm.toHom := by
  induction walk with
  | nil => simp [inverseSizedWalk]
  | @cons u w v edge tail ih =>
    rw [inverseSizedWalk]
    dsimp only
    rw [ih]
    apply SimpleGraph.Walk.ext_support
    have copied := SimpleGraph.Walk.support_copy (tail.map (sizedIso tables vertices same m size).symm.toHom)
      (getSized_numbering tables vertices same m size w).symm rfl
    have iso_apply (x : Fin m) : (sizedIso tables vertices same m size).symm.toHom x=
        (sizedNumbering tables vertices same m size).symm x := rfl
    simpa only [SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_map,List.map_cons,iso_apply]
      using congrArg (List.cons ((sizedNumbering tables vertices same m size).symm u)) copied

theorem inverseSizedWalk_count {u v : Fin m} (walk : (sizedGraph tables vertices m size).value.graph.Walk u v) :
    (inverseSizedWalk tables vertices same m size walk).events.length ≤ (14*(m+1)+2)*(walk.length+1) := by
  induction walk with
  | @nil u =>
    have head := getVertex_count tables vertices ⟨u.val,by rw [←size];exact u.isLt⟩
    rw [inverseSizedWalk]
    dsimp only [getSized]
    simp only [List.length_append,List.length_cons,List.length_nil,SimpleGraph.Walk.length_nil]
    omega
  | @cons u w v edge tail ih =>
    have head := getVertex_count tables vertices ⟨w.val,by rw [←size];exact w.isLt⟩
    rw [inverseSizedWalk]
    dsimp only [getSized]
    simp only [List.length_append,List.length_cons,List.length_nil,SimpleGraph.Walk.length_cons]
    have bound : (getVertex tables vertices ⟨w.val,by rw [←size];exact w.isLt⟩).events.length ≤ 14*(m+1) := by omega
    nlinarith

theorem inverseSizedWalk_words {u v : Fin m} (walk : (sizedGraph tables vertices m size).value.graph.Walk u v)
    (K : ℕ) (dimension : n+requests+m+3 ≤ K) :
    WordsWithin K (inverseSizedWalk tables vertices same m size walk).events := by
  have one : 1 ≤ K := by omega
  induction walk with
  | @nil u =>
    have head := getSized_words tables vertices m size u K dimension
    have index : u.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := u.isLt;omega)
    rw [inverseSizedWalk]
    dsimp only
    simp_all [wordsWithin_append,wordsWithin_cons]
  | @cons u w v edge tail ih =>
    have head := getSized_words tables vertices m size w K dimension
    have index : w.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := w.isLt;omega)
    rw [inverseSizedWalk]
    dsimp only
    simp_all [wordsWithin_append,wordsWithin_cons]

def inverseSizedPath {u v : Fin m} (path : (sizedGraph tables vertices m size).value.graph.Path u v) :
    Traced ((graph tables.graphData).Path ((sizedNumbering tables vertices same m size).symm u)
      ((sizedNumbering tables vertices same m size).symm v)) :=
  let walk := inverseSizedWalk tables vertices same m size path.val
  have simple : walk.value.IsPath := by
    rw [inverseSizedWalk_value]
    exact (path.map (sizedIso tables vertices same m size).symm.toHom (sizedIso tables vertices same m size).symm.injective).property
  ⟨⟨walk.value,simple⟩,walk.events⟩

theorem inverseSizedPath_value {u v : Fin m} (path : (sizedGraph tables vertices m size).value.graph.Path u v) :
    (inverseSizedPath tables vertices same m size path).value=
      path.map (sizedIso tables vertices same m size).symm.toHom (sizedIso tables vertices same m size).symm.injective := by
  apply Subtype.ext
  exact inverseSizedWalk_value tables vertices same m size path.val

end Inverse
end BuyAtBulk.Computation.Runtime.Original
