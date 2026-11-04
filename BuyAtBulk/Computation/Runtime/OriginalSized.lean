import BuyAtBulk.Computation.Runtime.OriginalPrices
import BuyAtBulk.Computation.Runtime.OriginalTransport
import BuyAtBulk.Computation.Runtime.Weights

/-! Reduction dimensions come from the actual enumerated buffer. All dense
loops take the cached numerical dimension explicitly. Equalities to the
canonical model size are used only in erased correctness proofs. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.Computation.Runtime.Original
open BuyAtBulk.NodeReduction BuyAtBulk.Computation.StoredOriginal
open scoped BuyAtBulk.Computation.NodeReduction
open Rational
variable {n resources requests : ℕ} (tables : Tables n resources requests)

def listLength {α : Type} : List α → Traced ℕ
  | [] => emit .write [1] 0
  | _::rest =>
    let previous := listLength rest
    let count := previous.value+1
    ⟨count,previous.events++[⟨.natAdd,[previous.value.size,1,count.size]⟩,⟨.write,[count.size]⟩]⟩
@[simp] theorem listLength_value {α : Type} (xs : List α) : (listLength xs).value=xs.length := by
  induction xs <;> simp_all [listLength]
@[simp] theorem listLength_count {α : Type} (xs : List α) : (listLength xs).events.length=2*xs.length+1 := by
  induction xs <;> simp_all [listLength];omega

def getSized (vertices : List (Vertex tables.graphData)) (m : ℕ) (size : m=vertices.length)
    (i : Fin m) : Traced (Vertex tables.graphData) :=
  getVertex tables vertices ⟨i.val,by rw [←size];exact i.isLt⟩
@[simp] theorem getSized_value (vertices : List (Vertex tables.graphData)) (m : ℕ) (size : m=vertices.length)
    (i : Fin m) : (getSized tables vertices m size i).value=vertices[i.val]'(by rw [←size];exact i.isLt) := by
  exact getVertex_value tables vertices _

def sizedNumbering (vertices : List (Vertex tables.graphData)) (same : vertices=modelVertices tables)
    (m : ℕ) (size : m=vertices.length) : Vertex tables.graphData ≃ Fin m :=
  (modelNumbering tables).trans (finCongr (size.trans (congrArg List.length same)).symm)

theorem getSized_numbering (vertices : List (Vertex tables.graphData)) (same : vertices=modelVertices tables)
    (m : ℕ) (size : m=vertices.length) (i : Fin m) :
    (getSized tables vertices m size i).value=(sizedNumbering tables vertices same m size).symm i := by
  subst vertices
  subst m
  exact enumeratedGet_value tables (modelVertices tables) rfl i

def sizedCell (vertices : List (Vertex tables.graphData)) (m : ℕ) (size : m=vertices.length)
    (u v : Fin m) : Traced Bool :=
  let a := getSized tables vertices m size u
  let b := getSized tables vertices m size v
  let result := adjacent tables a.value b.value
  ⟨result.value,[⟨.scan,[v.val.size]⟩]++a.events++b.events++result.events++[⟨.write,[u.val.size,v.val.size,1]⟩]⟩
@[simp] theorem sizedCell_value (vertices : List (Vertex tables.graphData)) (m : ℕ) (size : m=vertices.length)
    (u v : Fin m) : (sizedCell tables vertices m size u v).value=
      decide ((graph tables.graphData).Adj (vertices[u.val]'(by rw [←size];exact u.isLt))
        (vertices[v.val]'(by rw [←size];exact v.isLt))) := by
  simp only [sizedCell,adjacent_value,getSized_value]

def sizedGraph (vertices : List (Vertex tables.graphData)) (m : ℕ) (size : m=vertices.length) :
    Traced (ShortestPath.GraphEncoding m) :=
  let indices := indexList m
  let cells := Vector.ofFn fun u : Fin m=>Vector.ofFn fun v : Fin m=>sizedCell tables vertices m size u v
  let adjacency := cells.map (fun row=>row.map Traced.value)
  let result : ShortestPath.GraphEncoding m := {
    adjacency := adjacency
    symmetric := by
      intro u v
      simp only [adjacency,cells,Vector.getElem_map,Vector.getElem_ofFn,sizedCell_value]
      exact Bool.decide_congr ((graph tables.graphData).adj_comm _ _)
    diagonal := by
      intro u
      simp only [adjacency,cells,Vector.getElem_map,Vector.getElem_ofFn,sizedCell_value]
      simp }
  ⟨result,indices.events++indices.value.flatMap (fun u=>[⟨Operation.scan,[u.val.size]⟩,⟨.write,[u.val.size,m.size]⟩]++
    indices.value.flatMap (fun v=>cells[u.val][v.val].events))⟩

theorem sizedCell_count (vertices : List (Vertex tables.graphData)) (m : ℕ) (size : m=vertices.length)
    (u v : Fin m) : (sizedCell tables vertices m size u v).events.length ≤ 50*(m+1) := by
  have a := getVertex_count tables vertices ⟨u.val,by rw [←size];exact u.isLt⟩
  have b := getVertex_count tables vertices ⟨v.val,by rw [←size];exact v.isLt⟩
  have c := adjacent_count tables (getSized tables vertices m size u).value (getSized tables vertices m size v).value
  simp only [sizedCell,getSized,List.length_append,List.length_cons,List.length_nil]
  dsimp only [getSized] at c
  have length := size.symm
  omega

theorem sizedGraph_count (vertices : List (Vertex tables.graphData)) (m : ℕ) (size : m=vertices.length) :
    (sizedGraph tables vertices m size).events.length ≤ 50*(m+1)*m^2+5*m := by
  have per (u : Fin m) : ((List.finRange m).flatMap fun v=>(sizedCell tables vertices m size u v).events).length ≤
      50*(m+1)*m := by
    rw [List.length_flatMap]
    calc
      _ ≤ ((List.finRange m).map fun _=>50*(m+1)).sum := List.sum_le_sum (fun v _=>sizedCell_count tables vertices m size u v)
      _ = _ := by simp [Nat.mul_comm]
  have all : ((List.finRange m).flatMap fun u=>[⟨Operation.scan,[u.val.size]⟩,⟨.write,[u.val.size,m.size]⟩]++
      (List.finRange m).flatMap (fun v=>(sizedCell tables vertices m size u v).events)).length ≤
      m*(2+50*(m+1)*m) := by
    rw [List.length_flatMap]
    calc
      _ ≤ ((List.finRange m).map fun _=>2+50*(m+1)*m).sum := by
        apply List.sum_le_sum
        intro u _
        simp only [List.length_append,List.length_cons,List.length_nil]
        exact Nat.add_le_add_left (per u) 2
      _ = _ := by simp [Nat.mul_comm]
  simp only [sizedGraph,List.length_append,indexList_count,indexList_value,Vector.getElem_ofFn]
  nlinarith

theorem listLength_words {α : Type} (xs : List α) (K : ℕ) (size : xs.length+2 ≤ K) :
    WordsWithin K (listLength xs).events := by
  induction xs with
  | nil => simp [listLength,emit,WordsWithin];omega
  | cons x rest ih =>
    have tail := ih (by simp only [List.length_cons] at size;omega)
    have before : rest.length.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by simp only [List.length_cons] at size;omega)
    have after : (rest.length+1).size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by simp only [List.length_cons] at size;omega)
    have one : 1 ≤ K := by simp only [List.length_cons] at size;omega
    simp_all [listLength,wordsWithin_append,wordsWithin_cons]

theorem getSized_words (vertices : List (Vertex tables.graphData)) (m : ℕ) (size : m=vertices.length)
    (i : Fin m) (K : ℕ) (dimension : n+requests+m+3 ≤ K) :
    WordsWithin K (getSized tables vertices m size i).events :=
  getVertex_words tables vertices _ K (by simpa only [size] using dimension)

theorem sizedCell_words (vertices : List (Vertex tables.graphData)) (m : ℕ) (size : m=vertices.length)
    (u v : Fin m) (K : ℕ) (dimension : n+requests+m+3 ≤ K) :
    WordsWithin K (sizedCell tables vertices m size u v).events := by
  have a := getSized_words tables vertices m size u K dimension
  have b := getSized_words tables vertices m size v K dimension
  have c := adjacent_words tables (getSized tables vertices m size u).value (getSized tables vertices m size v).value K (by omega)
  have ui : u.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := u.isLt;omega)
  have vi : v.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := v.isLt;omega)
  have one : 1 ≤ K := by omega
  simp_all [sizedCell,wordsWithin_append,wordsWithin_cons]

theorem sizedGraph_words (vertices : List (Vertex tables.graphData)) (m : ℕ) (size : m=vertices.length)
    (K : ℕ) (dimension : n+requests+m+3 ≤ K) : WordsWithin K (sizedGraph tables vertices m size).events := by
  have indices := indexList_words m K (by omega)
  have mi : m.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  simp only [sizedGraph,wordsWithin_append,indexList_value,Vector.getElem_ofFn]
  refine ⟨indices,?_⟩
  intro event member word present
  obtain ⟨u,_,mem⟩ := List.mem_flatMap.mp member
  have ui : u.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := u.isLt;omega)
  have row : WordsWithin K ([⟨Operation.scan,[u.val.size]⟩,⟨.write,[u.val.size,m.size]⟩]++
      (List.finRange m).flatMap (fun v=>(sizedCell tables vertices m size u v).events)) := by
    simp only [wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
      or_false,forall_eq_or_imp,forall_eq,and_true]
    refine ⟨⟨ui,ui,mi⟩,?_⟩
    intro e mem w present
    obtain ⟨v,_,mem⟩ := List.mem_flatMap.mp mem
    exact sizedCell_words tables vertices m size u v K dimension e mem w present
  exact row event mem word present

def sizedIso (vertices : List (Vertex tables.graphData)) (same : vertices=modelVertices tables)
    (m : ℕ) (size : m=vertices.length) : (graph tables.graphData) ≃g (sizedGraph tables vertices m size).value.graph where
  toEquiv := sizedNumbering tables vertices same m size
  map_rel_iff' := by
    intro u v
    dsimp only [sizedGraph,ShortestPath.GraphEncoding.graph]
    simp only [Vector.getElem_map,Vector.getElem_ofFn]
    simp only [sizedCell,adjacent_value,getSized_numbering tables vertices same,
      Fin.eta,Equiv.symm_apply_apply,decide_eq_true_eq]

def sizedPriceCell (vertices : List (Vertex tables.graphData)) (m : ℕ) (size : m=vertices.length)
    (values : Vector ℚ resources) (fallback : ℚ) (i : Fin m) : Traced ℚ :=
  let vertex := getSized tables vertices m size i
  let price := resourceValue tables values fallback vertex.value
  ⟨price.value,[⟨.scan,[i.val.size]⟩]++vertex.events++price.events++[⟨.write,[i.val.size,(Code.ofRat price.value).bits]⟩]⟩

def sizedPrices (vertices : List (Vertex tables.graphData)) (m : ℕ) (size : m=vertices.length)
    (values : Vector ℚ resources) (fallback : ℚ) : Traced (Vector ℚ m) :=
  Weights.materialize (sizedPriceCell tables vertices m size values fallback) (fun q=>(Code.ofRat q).bits)

theorem sizedPrices_cost (vertices : List (Vertex tables.graphData)) (same : vertices=modelVertices tables)
    (m : ℕ) (size : m=vertices.length) (values : Vector ℚ resources) (i : Fin m) :
    (sizedPrices tables vertices m size values 0).value[i.val]=
      OriginalPipeline.resourceCost tables.graphData (fun a=>values[a.val])
        ((sizedNumbering tables vertices same m size).symm i) := by
  simp only [sizedPrices,Weights.materialize_get,sizedPriceCell,
    getSized_numbering tables vertices same,resourceCost_value]

theorem sizedPriceCell_count (vertices : List (Vertex tables.graphData)) (m : ℕ) (size : m=vertices.length)
    (values : Vector ℚ resources) (fallback : ℚ) (i : Fin m) :
    (sizedPriceCell tables vertices m size values fallback i).events.length ≤ 50*(m+resources+1) := by
  have vertex := getVertex_count tables vertices ⟨i.val,by rw [←size];exact i.isLt⟩
  have price := resourceValue_count tables values fallback (getSized tables vertices m size i).value
  simp only [sizedPriceCell,getSized,List.length_append,List.length_cons,List.length_nil]
  dsimp only [getSized] at price
  have length := size.symm
  omega

theorem sizedPrices_count (vertices : List (Vertex tables.graphData)) (m : ℕ) (size : m=vertices.length)
    (values : Vector ℚ resources) (fallback : ℚ) :
    (sizedPrices tables vertices m size values fallback).events.length ≤ m*(50*(m+resources+1)+2)+1 :=
  Weights.materialize_count _ _ _ (sizedPriceCell_count tables vertices m size values fallback)

theorem sizedPriceCell_words (vertices : List (Vertex tables.graphData)) (m : ℕ) (size : m=vertices.length)
    (values : Vector ℚ resources) (fallback : ℚ) (i : Fin m) (K : ℕ)
    (dimension : n+requests+resources+m+3 ≤ K)
    (inputs : ∀ a : Fin resources,(Code.ofRat values[a.val]).bits ≤ K)
    (default : (Code.ofRat fallback).bits ≤ K) :
    WordsWithin K (sizedPriceCell tables vertices m size values fallback i).events := by
  have vertex := getSized_words tables vertices m size i K (by omega)
  have price := resourceValue_words tables values fallback (getSized tables vertices m size i).value K (by omega) inputs default
  have output := resourceValue_output_bits tables values fallback (getSized tables vertices m size i).value K inputs default
  have index : i.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := i.isLt;omega)
  simp_all [sizedPriceCell,wordsWithin_append,wordsWithin_cons]

theorem sizedPrices_words (vertices : List (Vertex tables.graphData)) (m : ℕ) (size : m=vertices.length)
    (values : Vector ℚ resources) (fallback : ℚ) (K : ℕ)
    (dimension : n+requests+resources+m+3 ≤ K)
    (inputs : ∀ a : Fin resources,(Code.ofRat values[a.val]).bits ≤ K)
    (default : (Code.ofRat fallback).bits ≤ K) :
    WordsWithin K (sizedPrices tables vertices m size values fallback).events := by
  apply Weights.materialize_words
  · omega
  · exact fun i=>sizedPriceCell_words tables vertices m size values fallback i K dimension inputs default
  · intro i
    exact resourceValue_output_bits tables values fallback (getSized tables vertices m size i).value K inputs default

end BuyAtBulk.Computation.Runtime.Original
