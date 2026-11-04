import Mathlib.Algebra.BigOperators.Fin
import BuyAtBulk.Computation.Runtime.OriginalNumeric
import BuyAtBulk.Computation.Runtime.OriginalLabels
import BuyAtBulk.Computation.Runtime.Weights

/-! Reading an explicitly supplied original path list and computing its exact
length metadata. All resource searches, list traversals and rational sums are
instrumented; no compact-flow decomposition is needed by this entry point. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace BuyAtBulk.Computation.Runtime.Supplied
open Rational BuyAtBulk.NodeReduction BuyAtBulk.Computation.StoredOriginal
open Original
open scoped BuyAtBulk.Computation.NodeReduction
variable {n resources h : ℕ} (tables : Tables n resources h)

def occurs (vertex : Vertex tables.graphData) {u v : Fin n} : tables.graphData.graph.Walk u v → Traced Bool
  | .nil =>
    let node := vertexEqual tables vertex (.original u)
    ⟨node.value,[⟨.branch,[1]⟩]++node.events⟩
  | @SimpleGraph.Walk.cons _ _ u w v edge tail =>
    let node := vertexEqual tables vertex (.original u)
    let link := vertexEqual tables vertex (.edge s(u,w))
    let next := occurs vertex tail
    ⟨node.value || link.value || next.value,
      [⟨.branch,[1]⟩]++node.events++link.events++next.events++[⟨.branch,[1,1]⟩,⟨.branch,[1,1]⟩]⟩

 theorem occurs_resource (a : Fin resources) {u v : Fin n} (walk : tables.graphData.graph.Walk u v) :
    (occurs tables (resourceVertex tables.graphData a) walk).value =
      match tables.graphData.location a with
      | .inl x => decide (x ∈ walk.support)
      | .inr e => decide (e ∈ walk.edges) := by
  induction walk with
  | nil =>
    cases loc : tables.location[a.val] <;>
      simp [occurs,resourceVertex,Tables.graphData,loc,SimpleGraph.Walk.support,SimpleGraph.Walk.edges]
  | @cons u w v edge tail ih =>
    cases loc : tables.location[a.val] <;>
      simp_all [occurs,resourceVertex,Tables.graphData,SimpleGraph.Walk.support,SimpleGraph.Walk.edges]

 theorem occurs_count (vertex : Vertex tables.graphData) {u v : Fin n} (walk : tables.graphData.graph.Walk u v) :
    (occurs tables vertex walk).events.length ≤ 50*(walk.length+1) := by
  induction walk with
  | @nil u =>
    have := vertexEqual_count tables vertex (.original u)
    simp only [occurs,List.length_append,List.length_cons,List.length_nil,SimpleGraph.Walk.length_nil]
    omega
  | @cons u w v edge tail ih =>
    have a := vertexEqual_count tables vertex (.original u)
    have b := vertexEqual_count tables vertex (.edge s(u,w))
    simp only [occurs,List.length_append,List.length_cons,List.length_nil,SimpleGraph.Walk.length_cons]
    omega

 theorem occurs_words (vertex : Vertex tables.graphData) {u v : Fin n} (walk : tables.graphData.graph.Walk u v)
    (K : ℕ) (dim : n+h+3 ≤ K) : WordsWithin K (occurs tables vertex walk).events := by
  have one : 1 ≤ K := by omega
  induction walk with
  | @nil u =>
    have a := vertexEqual_words tables vertex (.original u) K dim
    simp_all [occurs,wordsWithin_append,wordsWithin_cons]
  | @cons u w v edge tail ih =>
    have a := vertexEqual_words tables vertex (.original u) K dim
    have b := vertexEqual_words tables vertex (.edge s(u,w)) K dim
    simp_all [occurs,wordsWithin_append,wordsWithin_cons]

def resourceTerm {u v : Fin n} (walk : tables.graphData.graph.Walk u v) (a : Fin resources) : Traced ℚ :=
  let found := occurs tables (resourceVertex tables.graphData a) walk
  let price := readRat tables.length a
  ⟨if found.value then price.value else 0,
    [⟨.read,[a.val.size,n.size,n.size]⟩]++found.events++price.events++[⟨.branch,[1]⟩]⟩

def pathCost (i : Fin h) (path : tables.graphData.graph.Path (tables.graphData.source i) (tables.graphData.target i)) : Traced ℚ :=
  let terms := Weights.materialize (resourceTerm tables path.val) (fun q => (Code.ofRat q).bits)
  let result := ratSum terms.value.toList
  ⟨result.value,terms.events++result.events⟩

 theorem pathCost_value (i : Fin h) (path : tables.graphData.graph.Path (tables.graphData.source i) (tables.graphData.target i)) :
    (pathCost tables i path).value = OriginalPipeline.pathResourceCost tables.graphData tables.graphData.length i path := by
  simp only [pathCost,ratSum_value,OriginalPipeline.pathResourceCost]
  simp only [Weights.materialize,Vector.toList_map,Vector.toList_ofFn,List.map_ofFn,Fin.sum_ofFn]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Function.comp_def,Weights.materialize_get,resourceTerm,occurs_resource,readRat,emit_value,OriginalPipeline.usesResource]
  congr 1
  split <;> simp_all only [decide_eq_decide]

 theorem resourceTerm_bits {u v : Fin n} (walk : tables.graphData.graph.Walk u v) (a : Fin resources)
    (L : ℕ) (constant : 3 ≤ L) (bits : ∀ a : Fin resources,(Code.ofRat tables.length[a.val]).bits ≤ L) :
    (Code.ofRat (resourceTerm tables walk a).value).bits ≤ L := by
  simp only [resourceTerm,readRat,emit_value]
  split
  · exact bits a
  · have zero : (Code.ofRat 0).bits=3 := by decide
    omega

 theorem pathCost_count (i : Fin h) (path : tables.graphData.graph.Path (tables.graphData.source i) (tables.graphData.target i)) :
    (pathCost tables i path).events.length ≤ resources*(50*(n+1)+11)+3 := by
  have len : path.val.length < n := by simpa using path.property.length_lt
  have terms := Weights.materialize_count (resourceTerm tables path.val) (fun q => (Code.ofRat q).bits)
    (50*(n+1)+3) (by
      intro a
      have occ := occurs_count tables (resourceVertex tables.graphData a) path.val
      simp only [resourceTerm,List.length_append,List.length_cons,List.length_nil,readRat,emit_length]
      omega)
  simp only [pathCost,List.length_append,ratSum_count,Vector.length_toList]
  nlinarith

 def pathWordBudget (n resources h L : ℕ) := n+resources+h+L+(8*resources+6)*(L+6)+20
 def pathOutputBudget (resources L : ℕ) := 2*(2*resources+1)*(L+6)+2

 theorem pathCost_words (i : Fin h) (path : tables.graphData.graph.Path (tables.graphData.source i) (tables.graphData.target i))
    (L : ℕ) (constant : 5 ≤ L) (bits : ∀ a : Fin resources,(Code.ofRat tables.length[a.val]).bits ≤ L) :
    WordsWithin (pathWordBudget n resources h L) (pathCost tables i path).events := by
  let K := pathWordBudget n resources h L
  have LK : L ≤ K := by dsimp[K,pathWordBudget];omega
  have one : 1 ≤ K := by dsimp[K,pathWordBudget];omega
  have ns : n.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[K,pathWordBudget];omega)
  have cells (a : Fin resources) : WordsWithin K (resourceTerm tables path.val a).events := by
    have occ := occurs_words tables (resourceVertex tables.graphData a) path.val K (by dsimp[K,pathWordBudget];omega)
    have aa : a.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := a.isLt;dsimp[K,pathWordBudget];omega)
    have p := (bits a).trans LK
    simp_all [resourceTerm,readRat,emit,wordsWithin_append,wordsWithin_cons]
  have terms := Weights.materialize_words (resourceTerm tables path.val) (fun q => (Code.ofRat q).bits) K
    (by dsimp[K,pathWordBudget];omega) cells (fun a => (resourceTerm_bits tables path.val a L (by omega) bits).trans LK)
  have termBits : ∀ q ∈ (Weights.materialize (resourceTerm tables path.val) (fun q => (Code.ofRat q).bits)).value.toList,
      (Code.ofRat q).bits+1 ≤ L+6 := by
    intro q mem
    obtain ⟨a,ha,rfl⟩ := List.mem_iff_getElem.mp mem
    have b := resourceTerm_bits tables path.val ⟨a,by simpa using ha⟩ L (by omega) bits
    change (Code.ofRat (Weights.materialize (resourceTerm tables path.val) (fun q => (Code.ofRat q).bits)).value[(⟨a,by simpa using ha⟩ : Fin resources).val]).bits+1 ≤ L+6
    rw [Weights.materialize_get]
    omega
  have sum := (ratSum_general_words _ (L+6) (by omega) termBits).mono
    (show _ ≤ K by simp only [Vector.length_toList];dsimp[K,pathWordBudget];omega)
  exact (wordsWithin_append _ _ _).mpr ⟨terms,sum⟩

 theorem pathCost_bits (i : Fin h) (path : tables.graphData.graph.Path (tables.graphData.source i) (tables.graphData.target i))
    (L : ℕ) (constant : 5 ≤ L) (bits : ∀ a : Fin resources,(Code.ofRat tables.length[a.val]).bits ≤ L) :
    (Code.ofRat (pathCost tables i path).value).bits ≤ pathOutputBudget resources L := by
  have termBits : ∀ q ∈ (Weights.materialize (resourceTerm tables path.val) (fun q => (Code.ofRat q).bits)).value.toList,
      (Code.ofRat q).bits+1 ≤ L+6 := by
    intro q mem
    obtain ⟨a,ha,rfl⟩ := List.mem_iff_getElem.mp mem
    have b := resourceTerm_bits tables path.val ⟨a,by simpa using ha⟩ L (by omega) bits
    change (Code.ofRat (Weights.materialize (resourceTerm tables path.val) (fun q => (Code.ofRat q).bits)).value[(⟨a,by simpa using ha⟩ : Fin resources).val]).bits+1 ≤ L+6
    rw [Weights.materialize_get]
    omega
  have sum := HelperExpressions.sum_rat_bits _ (L+6) (by omega) termBits
  simpa only [pathCost,ratSum_value,Vector.length_toList,pathOutputBudget] using sum

end BuyAtBulk.Computation.Runtime.Supplied
