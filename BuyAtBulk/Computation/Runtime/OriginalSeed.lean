import BuyAtBulk.Computation.Runtime.ShortestPathComplete
import BuyAtBulk.Computation.Runtime.Weights
import BuyAtBulk.Computation.OriginalInitialization

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.Computation.Runtime.Original
open BuyAtBulk.Computation.StoredOriginal
open Rational
variable {n resources requests : ℕ} (tables : Tables n resources requests)

abbrev originalInput : ShortestPath.GraphEncoding n :=
  ⟨tables.adjacency,tables.symmetric,tables.loopless⟩

def seedQuery (zeros : Vector ℚ n) (i : Fin requests) :
    Traced (Option (tables.graphData.graph.Path (tables.graphData.source i) (tables.graphData.target i))) :=
  let result := Runtime.ShortestPath.path (originalInput tables) zeros tables.source[i.val] tables.target[i.val]
  ⟨result.value,[⟨Operation.read,[i.val.size,n.size]⟩,⟨.read,[i.val.size,n.size]⟩]++result.events⟩

theorem seedQuery_value (zeros : Vector ℚ n) (same : zeros=Vector.replicate n 0) (i : Fin requests) :
    (seedQuery tables zeros i).value=seedPath tables i := by
  simp only [seedQuery,Runtime.ShortestPath.path_value,ShortestPath.GraphEncoding.path,seedPath,same]
  congr 1
  funext v
  simp

def seedZeros : Traced (Vector ℚ n) :=
  Weights.materialize (fun _ : Fin n => emit .write [(Code.ofRat (0:ℚ)).bits] (0:ℚ)) (fun q=>(Code.ofRat q).bits)

theorem seedZeros_value : (seedZeros (n:=n)).value=Vector.replicate n 0 := by
  apply Vector.ext
  intro i bound
  change (Weights.materialize _ _).value[(⟨i,bound⟩:Fin n).val]=_
  rw [Weights.materialize_get]
  simp [emit]

def seedQueryCount (n : ℕ) := (n+1)^2*(10*n^2+30*n+36)+3

theorem seedQuery_count (zeros : Vector ℚ n) (i : Fin requests) :
    (seedQuery tables zeros i).events.length≤seedQueryCount n := by
  have count := Runtime.ShortestPath.path_count (originalInput tables) zeros tables.source[i.val] tables.target[i.val]
  simp only [seedQuery,List.length_append,List.length_cons,List.length_nil,seedQueryCount]
  omega

theorem seedZeros_count : (seedZeros (n:=n)).events.length≤3*n+1 := by
  have count := Weights.materialize_count (fun _ : Fin n=>emit .write [(Code.ofRat (0:ℚ)).bits] (0:ℚ))
    (fun q=>(Code.ofRat q).bits) 1 (by intro i;rfl)
  simpa only [seedZeros,Nat.mul_comm] using count

def seedWordBudget (n h : ℕ) := 2*(5+Runtime.ShortestPath.labelBudget n 5)+9+n+n+h+5

theorem seedQuery_words (zeros : Vector ℚ n) (same : zeros=Vector.replicate n 0) (i : Fin requests) :
    WordsWithin (seedWordBudget n requests) (seedQuery tables zeros i).events := by
  have query := Runtime.ShortestPath.path_words (originalInput tables) zeros tables.source[i.val] tables.target[i.val]
    5 (by omega) (by intro v;simp [same,Code.bits,Code.ofRat])
  have sp := query.mono (show _≤seedWordBudget n requests by dsimp [seedWordBudget];omega)
  have ii : i.val.size≤seedWordBudget n requests := (Nat.size_le.mpr Nat.lt_two_pow_self).trans
    (by have := i.isLt;dsimp [seedWordBudget];omega)
  have ni : n.size≤seedWordBudget n requests := (Nat.size_le.mpr Nat.lt_two_pow_self).trans
    (by dsimp [seedWordBudget];omega)
  simp_all [seedQuery,wordsWithin_append,wordsWithin_cons]

theorem seedZeros_words (K : ℕ) (dimension : n+5≤K) : WordsWithin K (seedZeros (n:=n)).events := by
  have zero : (Code.ofRat (0:ℚ)).bits≤K := by norm_num [Code.ofRat,Code.bits];omega
  apply Weights.materialize_words
  · omega
  · intro i;simp [emit,wordsWithin_cons,zero]
  · intro i;exact zero

def seedEntriesTrace (zeros : Vector ℚ n) : List (Fin requests) →
    Traced (Option (List (Entry (G:=tables.graphData.graph) tables.graphData.source tables.graphData.target)))
  | [] => ⟨some [],[⟨.branch,[1]⟩,⟨.write,[1]⟩]⟩
  | i::rest =>
    let head := seedQuery tables zeros i
    match head.value with
    | none => ⟨none,[⟨.branch,[1]⟩,⟨.scan,[i.val.size]⟩]++head.events++[⟨.branch,[1]⟩,⟨.write,[1]⟩]⟩
    | some path =>
      let tail := seedEntriesTrace zeros rest
      ⟨tail.value.map (fun entries=>⟨i,1,path⟩::entries),
        [⟨.branch,[1]⟩,⟨.scan,[i.val.size]⟩]++head.events++[⟨.branch,[1]⟩]++tail.events++
          [⟨.branch,[1]⟩]++(if tail.value.isSome then [⟨.cons,[i.val.size,(Code.ofRat (1:ℚ)).bits]⟩] else [])⟩

theorem seedEntriesTrace_value (zeros : Vector ℚ n) (same : zeros=Vector.replicate n 0)
    (order : List (Fin requests)) : (seedEntriesTrace tables zeros order).value=seedEntries tables order := by
  induction order with
  | nil => rfl
  | cons i rest ih =>
    simp only [seedEntriesTrace,seedEntries,seedQuery_value tables zeros same]
    cases found : seedPath tables i <;> simp only [ih]

theorem seedEntriesTrace_count (zeros : Vector ℚ n) (order : List (Fin requests)) :
    (seedEntriesTrace tables zeros order).events.length≤(seedQueryCount n+6)*order.length+2 := by
  induction order with
  | nil => simp [seedEntriesTrace]
  | cons i rest ih =>
    have head := seedQuery_count tables zeros i
    simp only [seedEntriesTrace]
    split
    · simp only [List.length_append,List.length_cons,List.length_nil,List.length_cons] ; nlinarith
    · simp only [List.length_append,List.length_cons,List.length_nil]
      split <;> simp only [List.length_cons,List.length_nil] <;> nlinarith

theorem seedEntriesTrace_words (zeros : Vector ℚ n) (same : zeros=Vector.replicate n 0)
    (order : List (Fin requests)) :
    WordsWithin (seedWordBudget n requests) (seedEntriesTrace tables zeros order).events := by
  have one : 1≤seedWordBudget n requests := by dsimp [seedWordBudget];omega
  have wone : (Code.ofRat (1:ℚ)).bits≤seedWordBudget n requests := by norm_num [Code.ofRat,Code.bits];dsimp [seedWordBudget];omega
  induction order with
  | nil => simp [seedEntriesTrace,WordsWithin,one]
  | cons i rest ih =>
    have query := seedQuery_words tables zeros same i
    have index : i.val.size≤seedWordBudget n requests := (Nat.size_le.mpr Nat.lt_two_pow_self).trans
      (by have := i.isLt;dsimp [seedWordBudget];omega)
    simp only [seedEntriesTrace]
    split
    · simp_all [wordsWithin_append,wordsWithin_cons]
    · split <;> simp_all [wordsWithin_append,wordsWithin_cons]

def failedRequestTrace (zeros : Vector ℚ n) : List (Fin requests) → Traced (Option (Fin requests))
  | [] => ⟨none,[⟨.branch,[1]⟩]⟩
  | i::rest =>
    let query := seedQuery tables zeros i
    match query.value with
    | none => ⟨some i,[⟨.scan,[i.val.size]⟩]++query.events++[⟨.branch,[1]⟩,⟨.write,[i.val.size]⟩]⟩
    | some _ =>
      let tail := failedRequestTrace zeros rest
      ⟨tail.value,[⟨.scan,[i.val.size]⟩]++query.events++[⟨.branch,[1]⟩]++tail.events⟩

theorem failedRequestTrace_value (zeros : Vector ℚ n) (same : zeros=Vector.replicate n 0)
    (order : List (Fin requests)) : (failedRequestTrace tables zeros order).value=failedRequest tables order := by
  induction order with
  | nil => rfl
  | cons i rest ih =>
    simp only [failedRequestTrace,failedRequest,seedQuery_value tables zeros same]
    cases found : seedPath tables i <;> simp only [ih]

theorem failedRequestTrace_count (zeros : Vector ℚ n) (order : List (Fin requests)) :
    (failedRequestTrace tables zeros order).events.length≤(seedQueryCount n+3)*order.length+1 := by
  induction order with
  | nil => simp [failedRequestTrace]
  | cons i rest ih =>
    have head := seedQuery_count tables zeros i
    simp only [failedRequestTrace]
    split <;> simp only [List.length_append,List.length_cons,List.length_nil] <;> nlinarith

theorem failedRequestTrace_words (zeros : Vector ℚ n) (same : zeros=Vector.replicate n 0)
    (order : List (Fin requests)) :
    WordsWithin (seedWordBudget n requests) (failedRequestTrace tables zeros order).events := by
  have one : 1≤seedWordBudget n requests := by dsimp [seedWordBudget];omega
  induction order with
  | nil => simp [failedRequestTrace,WordsWithin,one]
  | cons i rest ih =>
    have query := seedQuery_words tables zeros same i
    have index : i.val.size≤seedWordBudget n requests := (Nat.size_le.mpr Nat.lt_two_pow_self).trans
      (by have := i.isLt;dsimp [seedWordBudget];omega)
    simp only [failedRequestTrace]
    split <;> simp_all [wordsWithin_append,wordsWithin_cons]

end BuyAtBulk.Computation.Runtime.Original
