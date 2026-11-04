import BuyAtBulk.Computation.Runtime.PhaseMetadata
import BuyAtBulk.UpperBound.ZeroLengthGraph

namespace BuyAtBulk.Computation.Runtime.StoredRounding
open BuyAtBulk.UpperBound
open Rational
variable {n : ℕ} (input : ShortestPath.GraphEncoding n)

def zeroAdjCell (physical : Vector ℚ n) (u v : Fin n) : Traced Bool := do
  let edge ← emit .read [u.val.size,v.val.size,1] input.adjacency[u.val][v.val]
  let a ← readRat physical u
  let aZero ← zeroTest a
  let b ← readRat physical v
  let bZero ← zeroTest b
  emit .branch [1,1,1] (edge && aZero && bZero)

@[simp] theorem zeroAdjCell_value (physical : Vector ℚ n) (u v : Fin n) :
    (zeroAdjCell input physical u v).value= (input.adjacency[u.val][v.val] && decide (physical[u.val]=0) && decide (physical[v.val]=0)) := rfl

def zeroInput (physical : Vector ℚ n) : Traced (ShortestPath.GraphEncoding n) :=
  let cells := Weights.materialize (fun u : Fin n =>
    Weights.materialize (zeroAdjCell input physical u) (fun _ => 1)) (fun _ => n)
  ⟨{adjacency:=cells.value,
    symmetric:=by
      intro u v
      simp only[cells,Weights.materialize_get,zeroAdjCell_value]
      rw[input.symmetric u v]
      simp[Bool.and_assoc,Bool.and_comm,Bool.and_left_comm],
    diagonal:=by
      intro u
      simp only[cells,Weights.materialize_get,zeroAdjCell_value,input.diagonal,Bool.false_and]},
    cells.events++[⟨.cons,[n.size,n.size]⟩]⟩

theorem zeroInput_graph (physical : Vector ℚ n) :
    (zeroInput input physical).value.graph=zeroGraph input.graph (fun v => physical[v.val]) := by
  ext u v
  by_cases a : physical[u.val]=0 <;>by_cases b : physical[v.val]=0 <;>
    simp[zeroInput,ShortestPath.GraphEncoding.graph,zeroGraph,Weights.materialize,zeroAdjCell_value,a,b]

theorem zeroInput_count (physical : Vector ℚ n) : (zeroInput input physical).events.length ≤ n*(8*n+3)+2 := by
  have inner (u : Fin n) : (Weights.materialize (zeroAdjCell input physical u) (fun _ => 1)).events.length ≤ 8*n+1 := by
    simpa only[Nat.mul_comm] using Weights.materialize_count (zeroAdjCell input physical u) (fun _ => 1) 6 (by intro;rfl)
  have outer := Weights.materialize_count (fun u : Fin n => Weights.materialize (zeroAdjCell input physical u) (fun _ => 1))
    (fun _ => n) (8*n+1) inner
  simp only[zeroInput,List.length_append,List.length_cons,List.length_nil]
  simp only[Nat.add_assoc,Nat.reduceAdd] at outer
  omega

theorem zeroInput_words (physical : Vector ℚ n) (L : ℕ) (inputs : ∀ v : Fin n, (Code.ofRat physical[v.val]).bits ≤ L) :
    WordsWithin (n+L+5) (zeroInput input physical).events := by
  let K := n+L+5
  have ni : n ≤ K := by dsimp[K];omega
  have one : 1 ≤ K := by dsimp[K];omega
  have scalar : L ≤ K := by dsimp[K];omega
  have nn := (Nat.size_le.mpr Nat.lt_two_pow_self : n.size ≤ n).trans ni
  have cell (u v : Fin n) : WordsWithin K (zeroAdjCell input physical u v).events := by
    have ui := ((Nat.size_le.mpr Nat.lt_two_pow_self : u.val.size ≤ u.val).trans (Nat.le_of_lt u.isLt)).trans ni
    have vi := ((Nat.size_le.mpr Nat.lt_two_pow_self : v.val.size ≤ v.val).trans (Nat.le_of_lt v.isLt)).trans ni
    have au := (inputs u).trans scalar
    have bv := (inputs v).trans scalar
    simp only[zeroAdjCell,Traced.bind_events,Traced.bind_value,readRat,emit_value,zeroTest,emit,wordsWithin_append,
      wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
    dsimp[K] at *
    aesop
  have rows (u : Fin n) := Weights.materialize_words (zeroAdjCell input physical u) (fun _ => 1) K ni (cell u) (by intro;exact one)
  have matrix := Weights.materialize_words (fun u : Fin n => Weights.materialize (zeroAdjCell input physical u) (fun _ => 1))
    (fun _ => n) K ni rows (by intro;exact ni)
  simpa only[zeroInput,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
    or_false,forall_eq_or_imp,forall_eq,and_true] using And.intro matrix (And.intro nn nn)

end BuyAtBulk.Computation.Runtime.StoredRounding
