import BuyAtBulk.Computation.Runtime.FreeRoutes

namespace BuyAtBulk.Computation.Runtime.StoredRounding
open BuyAtBulk.UpperBound
open Rational
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

structure Output (source target : Vector (Fin n) h) where
  bought : Vector Bool n
  routes : List (StoredBatch.Entry input source target)

def decodeOutput (source target : Vector (Fin n) h) (output : Output input source target) :
    Rounding.Output input.graph (fun i => source[i.val]) (fun i => target[i.val]) :=
  ⟨StoredState.boughtSet output.bought,output.routes⟩

def freeRun (buying physical : Vector ℚ n) (source target : Vector (Fin n) h) (lengths : Vector ℚ h) :
    Traced (Option (Output input source target)) :=
  let state := zeroState input buying
  let indices := indexList h
  let result := freeRoutes input physical source target lengths state.value indices.value
  let output := result.value.map fun routes => (⟨state.value.bought,routes⟩ : Output input source target)
  ⟨output,state.events++indices.events++result.events++[⟨.branch,[1]⟩,⟨.cons,[n.size,h.size]⟩]⟩

theorem freeRun_value (buying physical : Vector ℚ n) (source target : Vector (Fin n) h) (lengths : Vector ℚ h) :
    (freeRun input buying physical source target lengths).value.map (decodeOutput input source target)=
      (Rounding.freeRoutes input.graph (Equiv.refl _) (fun v => physical[v.val]) (fun i => source[i.val]) (fun i => target[i.val])
        (fun i => lengths[i.val]) (Rounding.zeroState input.graph (Equiv.refl _) (fun v => buying[v.val])) (List.finRange h)).map
        (fun entries => (⟨(Rounding.zeroState input.graph (Equiv.refl _) (fun v => buying[v.val])).bought,entries⟩ : Rounding.Output input.graph _ _)) := by
  simp only[freeRun,indexList_value,freeRoutes_value,zeroState_value,Option.map_map]
  congr 1
  funext routes
  change Rounding.Output.mk _ routes = Rounding.Output.mk _ routes
  congr 1
  exact congrArg (fun state : RoundingState input.graph => state.bought) (zeroState_value input buying)

def freeCount (n h : ℕ) := 4*n+2+3*h+h*(AttachmentQueries.routeBudget n+12*n+8)+3

theorem freeRun_count (buying physical : Vector ℚ n) (source target : Vector (Fin n) h) (lengths : Vector ℚ h) :
    (freeRun input buying physical source target lengths).events.length ≤ freeCount n h := by
  have state := zeroState_count input buying
  have routes := freeRoutes_count input physical source target lengths (zeroState input buying).value (List.finRange h)
  simp only[List.length_finRange] at routes
  simp only[freeRun,List.length_append,List.length_cons,List.length_nil,indexList_count,indexList_value]
  unfold freeCount
  omega

def freeWords (n h L : ℕ) := StoredAttachment.wordBudget n 0 L+n+h+L+10

theorem freeRun_words (buying physical : Vector ℚ n) (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (L : ℕ) (constant : 8 ≤ L)
    (buying_width : ∀ v : Fin n, (Code.ofRat buying[v.val]).bits ≤ L)
    (physical_width : ∀ v : Fin n, (Code.ofRat physical[v.val]).bits ≤ L)
    (lengths_width : ∀ i : Fin h, (Code.ofRat lengths[i.val]).bits ≤ L) :
    WordsWithin (freeWords n h L) (freeRun input buying physical source target lengths).events := by
  let K := freeWords n h L
  have ni : n ≤ K := by dsimp[K,freeWords];omega
  have hi : h ≤ K := by dsimp[K,freeWords];omega
  have one : 1 ≤ K := by dsimp[K,freeWords];omega
  have nn := (Nat.size_le.mpr Nat.lt_two_pow_self : n.size ≤ n).trans ni
  have hh := (Nat.size_le.mpr Nat.lt_two_pow_self : h.size ≤ h).trans hi
  have state := (zeroState_words input buying L buying_width).mono (show n+L+5 ≤ K by dsimp[K,freeWords];omega)
  have indices := indexList_words h K hi
  have routes := (freeRoutes_words input physical source target lengths (zeroState input buying).value (List.finRange h)
    L constant physical_width lengths_width).mono (show StoredAttachment.wordBudget n 0 L+n+h+10 ≤ K by dsimp[K,freeWords];omega)
  simp only[freeRun,indexList_value,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
    or_false,forall_eq_or_imp,forall_eq,and_true]
  aesop

end BuyAtBulk.Computation.Runtime.StoredRounding
