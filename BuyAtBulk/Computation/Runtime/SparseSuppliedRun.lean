import BuyAtBulk.Computation.Runtime.SparseSuppliedDecompose

/-! Complete request traversal and stored tagged output; the opening vector is
shared unchanged. Returned simple paths were allocated by flow extraction. -/
set_option maxHeartbeats 2400000
namespace BuyAtBulk.Computation.Runtime.SparseSupplied
open Rational StoredOriginal
variable {n h : ℕ} {G : SimpleGraph (Fin n)} (source target : Fin h → Fin n)

def prepend (i : Fin h) : FlowDecomposition.WeightedPaths G (source i) (target i) →
    List (Entry (G:=G) source target) → Traced (List (Entry (G:=G) source target))
  | [],tail => ⟨tail,[⟨.branch,[1]⟩]⟩
  | e::rest,tail =>
    let next := prepend i rest tail
    ⟨⟨i,e⟩::next.value,[⟨.branch,[1]⟩,⟨.scan,[1]⟩]++next.events++
      [⟨.cons,[i.val.size,(Code.ofRat e.1).bits,n.size]⟩]⟩

@[simp] theorem prepend_value (i : Fin h) (entries : FlowDecomposition.WeightedPaths G (source i) (target i))
    (tail : List (Entry (G:=G) source target)) :
    (prepend source target i entries tail).value=entries.map (fun e=>⟨i,e⟩)++tail := by
  induction entries <;> simp_all[prepend]

 theorem prepend_count (i : Fin h) (entries : FlowDecomposition.WeightedPaths G (source i) (target i))
    (tail : List (Entry (G:=G) source target)) :
    (prepend source target i entries tail).events.length=3*entries.length+1 := by
  induction entries <;> simp_all[prepend] <;> omega

 theorem prepend_words (i : Fin h) (entries : FlowDecomposition.WeightedPaths G (source i) (target i))
    (tail : List (Entry (G:=G) source target)) (K : ℕ) (indices : n+h+1 ≤ K)
    (bits : ∀ e∈entries,(Code.ofRat e.1).bits ≤ K) :
    WordsWithin K (prepend source target i entries tail).events := by
  have one : 1 ≤ K := by omega
  have ni : n.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have ii : i.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  induction entries with
  | nil => simp[prepend,WordsWithin,one]
  | cons e rest ih =>
    have tail := ih (fun e mem=>bits e (by simp[mem]))
    have eb := bits e (by simp)
    simp[prepend,wordsWithin_append,wordsWithin_cons,one,ni,ii,tail,eb]

variable (input : ShortestPath.GraphEncoding n)

def runRequests (entries : List (Entry (G:=input.graph) source target)) : List (Fin h) →
    Traced (Option (List (Entry (G:=input.graph) source target)))
  | [] => ⟨some [],[⟨.branch,[1]⟩,⟨.write,[1]⟩]⟩
  | i::indices =>
    let head := request input source target entries i
    let tail := runRequests entries indices
    let initial : List Event := [⟨.branch,[1]⟩,⟨.scan,[i.val.size]⟩]++head.events++tail.events++
      [⟨.branch,[1]⟩,⟨.branch,[1]⟩]
    match head.value,tail.value with
    | some paths,some rest =>
      let result := prepend source target i paths rest
      ⟨some result.value,initial++result.events⟩
    | _,_ => ⟨none,initial⟩

 /-- As in `Weights.materialize`, `finRange` denotes a fixed indexed loop:
its iterations are charged by `runRequests` scans, rather than an allocated
auxiliary runtime list. Output list allocation is charged by `prepend`. -/
 def run (entries : List (Entry (G:=input.graph) source target)) :=
  runRequests source target input entries (List.finRange h)

 theorem runRequests_value (entries : List (Entry (G:=input.graph) source target))
    (paths : ∀ i,FlowDecomposition.WeightedPaths input.graph (source i) (target i))
    (returned : ∀ i,(request input source target entries i).value=some (paths i))
    (indices : List (Fin h)) :
    (runRequests source target input entries indices).value=
      some (indices.flatMap fun i=>(paths i).map fun e=>⟨i,e⟩) := by
  induction indices with
  | nil => rfl
  | cons i rest ih => simp only [runRequests,returned,ih,prepend_value,List.flatMap_cons]

 def runCount (n k h : ℕ) := h*(5*k+1+compressCount n k+3*(n*n+1)+5)+2
 def runWords (n k h L : ℕ) := n+h+L+1+compressWords n k L+2*n*n*cellBits n k L+5

 theorem runRequests_count (entries : List (Entry (G:=input.graph) source target))
    (paths : ∀ i,FlowDecomposition.WeightedPaths input.graph (source i) (target i))
    (returned : ∀ i,(request input source target entries i).value=some (paths i))
    (support : ∀ i,(paths i).length ≤ n*n+1) (indices : List (Fin h)) :
    (runRequests source target input entries indices).events.length ≤ runCount n entries.length indices.length := by
  induction indices with
  | nil => simp[runRequests,runCount]
  | cons i rest ih =>
    have tail := runRequests_value source target input entries paths returned rest
    have head := request_count input source target entries i
    have size := support i
    simp only [runRequests,returned,tail,List.length_append,List.length_cons,List.length_nil,prepend_count]
    dsimp[runCount] at *
    nlinarith

 theorem runRequests_words (entries : List (Entry (G:=input.graph) source target))
    (paths : ∀ i,FlowDecomposition.WeightedPaths input.graph (source i) (target i))
    (returned : ∀ i,(request input source target entries i).value=some (paths i))
    (nonneg : ∀ e∈entries,0 ≤ e.2.1)
    (unit : ∀ i,((selectPaths source target entries i).map Prod.fst).sum=1)
    (L : ℕ) (constant : 3 ≤ L) (bits : ∀ e∈entries,(Code.ofRat e.2.1).bits ≤ L)
    (indices : List (Fin h)) :
    WordsWithin (runWords n entries.length h L) (runRequests source target input entries indices).events := by
  let K := runWords n entries.length h L
  have one : 1 ≤ K := by dsimp[K,runWords];omega
  have ii (i : Fin h) : i.val.size ≤ K :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[K,runWords];omega)
  induction indices with
  | nil => simp[runRequests,WordsWithin];dsimp[runWords];omega
  | cons i rest ih =>
    have tail := runRequests_value source target input entries paths returned rest
    have head := (request_words input source target entries i nonneg (unit i) L constant bits).mono
      (show _ ≤ K by dsimp[K,runWords];omega)
    have outputBits := compress_output_bits input (selectPaths source target entries i) (paths i)
      (selectPaths_nonneg source target entries nonneg i) (unit i)
      (by simpa using returned i) L constant (selected_bits source target i entries L bits)
    have length := selectPaths_length source target entries i
    have copied := prepend_words source target i (paths i)
      (rest.flatMap fun j=>(paths j).map fun e=>⟨j,e⟩) K
      (by dsimp[K,runWords];omega) (by
        intro e mem
        apply (outputBits e mem).trans
        apply Nat.le_trans (show 2*n*n*cellBits n (selectPaths source target entries i).length L+4 ≤
            2*n*n*cellBits n entries.length L+4 by unfold cellBits;gcongr)
        dsimp[K,runWords];omega)
    simp only [runRequests,returned,tail]
    change WordsWithin K _
    simpa [wordsWithin_append,wordsWithin_cons,one,ii,head,copied] using ih

end BuyAtBulk.Computation.Runtime.SparseSupplied
