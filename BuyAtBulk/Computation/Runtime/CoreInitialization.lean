import BuyAtBulk.Computation.Runtime.CoreRows
import BuyAtBulk.Computation.Core.Initialization

namespace BuyAtBulk.Computation.Runtime.StoredCore
open BuyAtBulk.UpperBound
open Rational
variable {n : ℕ} (input : ShortestPath.GraphEncoding n)

def markMany : List (Fin n) → StoredState.State input.graph → Traced (StoredState.State input.graph)
  | [],state => emit .branch [1] state
  | v::rest,state =>
    let marked := StoredState.mark input.graph state v
    let next := markMany rest marked.value
    ⟨next.value,[⟨.scan,[v.val.size]⟩,⟨.branch,[1]⟩]++marked.events++next.events⟩

theorem decode_markMany (nodes : List (Fin n)) (state : StoredState.State input.graph) :
    StoredState.decode input.graph (markMany input nodes state).value =
      {StoredState.decode input.graph state with bought := (StoredState.decode input.graph state).bought∪nodes.toFinset} := by
  induction nodes generalizing state with
  | nil => simp[markMany,emit]
  | cons v rest ih =>
    simp only[markMany,ih,StoredState.decode_mark,List.toFinset_cons]
    simp[Finset.insert_union,Finset.union_insert]

theorem markMany_count (nodes : List (Fin n)) (state : StoredState.State input.graph) :
    (markMany input nodes state).events.length ≤ nodes.length*(4*n+3)+1 := by
  induction nodes generalizing state with
  | nil => simp[markMany,emit]
  | cons v rest ih =>
    have marked := StoredState.mark_count input.graph state v
    have next := ih (StoredState.mark input.graph state v).value
    simp only[markMany,List.length_append,List.length_cons,List.length_nil]
    nlinarith

theorem markMany_words (nodes : List (Fin n)) (state : StoredState.State input.graph) :
    WordsWithin (n+1) (markMany input nodes state).events := by
  induction nodes generalizing state with
  | nil => simp[markMany,emit,WordsWithin]
  | cons v rest ih =>
    have marked := StoredState.mark_words input.graph state v (n+1) (by omega) (by omega)
    have next := ih (StoredState.mark input.graph state v).value
    have vi : v.val.size ≤ n+1 := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := v.isLt;omega)
    have one : 1 ≤ n+1 := by omega
    simp only[markMany,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
      or_false,forall_eq_or_imp,forall_eq,and_true]
    exact ⟨⟨⟨vi,one⟩,marked⟩,next⟩

def zeroCell (buying : Vector ℚ n) (flags : Vector Bool n) (v : Fin n) : Traced Bool := do
  let q ← readRat buying v
  let zero ← emit .ratCompare [(Code.ofRat q).bits,(Code.ofRat 0).bits] (decide (q=0))
  let before ← emit .read [v.val.size,1] flags[v.val]
  emit .branch [1,1] (before||zero)

@[simp] theorem zeroCell_value (buying : Vector ℚ n) (flags : Vector Bool n) (v : Fin n) :
    (zeroCell buying flags v).value= (flags[v.val] || decide (buying[v.val]=0)) := rfl

def initialState (buying : Vector ℚ n) (seed : Vector Bool n) (helperNodes : List (Fin n)) :
    Traced (StoredState.State input.graph) :=
  let seedState : StoredState.State input.graph := ⟨seed,[],[]⟩
  let marked := markMany input helperNodes seedState
  let flags := Weights.materialize (zeroCell buying marked.value.bought) (fun _ => 1)
  ⟨⟨flags.value,[],[]⟩,[⟨.cons,[n.size]⟩]++marked.events++flags.events++[⟨.cons,[n.size]⟩]⟩

theorem initialState_value (buying : Vector ℚ n) (seed : Vector Bool n) (helperNodes : List (Fin n)) :
    StoredState.decode input.graph (initialState input buying seed helperNodes).value =
      {bought := StoredState.boughtSet seed∪helperNodes.toFinset∪Core.zeroBuyingNodes (Equiv.refl _) (fun v => buying[v.val]),
        centers := [],edges := []} := by
  have marked := decode_markMany input helperNodes (⟨seed,[],[]⟩ : StoredState.State input.graph)
  have flags : StoredState.boughtSet (initialState input buying seed helperNodes).value.bought =
      StoredState.boughtSet seed∪helperNodes.toFinset∪Core.zeroBuyingNodes (Equiv.refl _) (fun v => buying[v.val]) := by
    ext v
    change v∈_ ↔ v∈_
    simp only[initialState,StoredState.mem_boughtSet,Weights.materialize_get,zeroCell_value,Bool.or_eq_true,
      decide_eq_true_eq,Finset.mem_union,Core.mem_zeroBuyingNodes]
    have same := congrArg (fun state => v∈state.bought) marked
    simp only[StoredState.decode,Finset.mem_union,StoredState.mem_boughtSet] at same
    rw[same]
  exact congrArg (fun bought => (⟨bought,[],[]⟩ : RoundingState input.graph)) flags

theorem initialState_count (buying : Vector ℚ n) (seed : Vector Bool n) (nodes : List (Fin n)) :
    (initialState input buying seed nodes).events.length ≤ nodes.length*(4*n+3)+6*n+4 := by
  have marked := markMany_count input nodes (⟨seed,[],[]⟩ : StoredState.State input.graph)
  have flags := Weights.materialize_count (zeroCell buying (markMany input nodes (⟨seed,[],[]⟩ : StoredState.State input.graph)).value.bought)
    (fun _ => 1) 4 (by intro v;rfl)
  simp only[initialState,List.length_append,List.length_cons,List.length_nil]
  omega

theorem initialState_words (buying : Vector ℚ n) (seed : Vector Bool n) (nodes : List (Fin n)) (L : ℕ)
    (inputs : ∀ v : Fin n, (Code.ofRat buying[v.val]).bits ≤ L) :
    WordsWithin (n+L+5) (initialState input buying seed nodes).events := by
  let K := n+L+5
  have one : 1 ≤ K := by dsimp[K];omega
  have ni : n ≤ K := by dsimp[K];omega
  have nn := (Nat.size_le.mpr Nat.lt_two_pow_self : n.size ≤ n).trans ni
  have marked := (markMany_words input nodes (⟨seed,[],[]⟩ : StoredState.State input.graph)).mono (show n+1 ≤ K by dsimp[K];omega)
  have flags := Weights.materialize_words
    (zeroCell buying (markMany input nodes (⟨seed,[],[]⟩ : StoredState.State input.graph)).value.bought)
    (fun _ => 1) K ni (by
      intro v
      have vi : v.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := v.isLt;dsimp[K];omega)
      have qi := (inputs v).trans (show L ≤ K by dsimp[K];omega)
      have zero : (Code.ofRat 0).bits=3 := by decide
      simp only[zeroCell,Traced.bind_events,Traced.bind_value,emit_value,readRat,emit,zero,wordsWithin_append,
        wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
      dsimp[K] at *
      aesop) (by intro;exact one)
  simp only[initialState,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_singleton,forall_eq,and_true]
  aesop

end BuyAtBulk.Computation.Runtime.StoredCore
