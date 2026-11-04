import BuyAtBulk.Computation.Runtime.SparseSuppliedSelect
import BuyAtBulk.Computation.Runtime.SparseSuppliedFlow
import BuyAtBulk.Computation.Runtime.FlowDecomposition

/-! Supplied paths are aggregated and decomposed by executed traced programs,
with positive, unit-mass output of at most n²+1 simple paths. -/
set_option maxHeartbeats 1800000
namespace BuyAtBulk.Computation.Runtime.SparseSupplied
open Rational StoredOriginal
variable {n : ℕ} (input : ShortestPath.GraphEncoding n)

def compress {s t : Fin n} (entries : FlowDecomposition.WeightedPaths input.graph s t) :
    Traced (Option (FlowDecomposition.WeightedPaths input.graph s t)) :=
  let matrix := aggregate entries
  let result := FlowExtract.decompose input matrix.value s t
  ⟨result.value,matrix.events++result.events⟩

theorem compress_correct {s t : Fin n} (entries : FlowDecomposition.WeightedPaths input.graph s t)
    (nonneg : ∀ e∈entries,0 ≤ e.1) (unit : (entries.map Prod.fst).sum=1) :
    ∃ output, (compress input entries).value=some output ∧
      (∀ e∈output,0<e.1) ∧ (output.map Prod.fst).sum=1 ∧
      (∀ u v,(output.map fun e=>e.1*CompactFlow.transportVisits e.2.val u v).sum ≤
        (entries.map fun e=>e.1*CompactFlow.transportVisits e.2.val u v).sum) ∧
      output.length ≤ n*n+1 := by
  have nonnegative : ∀ u v,0 ≤ FlowDecomposition.decodedFlow (Equiv.refl _) (aggregate entries).value u v := by
    intro u v
    simpa [FlowDecomposition.decodedFlow,FlowDecomposition.matrixFlow] using aggregate_nonneg entries nonneg u v
  have nonedge : ∀ u v,¬input.graph.Adj u v → FlowDecomposition.decodedFlow (Equiv.refl _) (aggregate entries).value u v=0 := by
    intro u v missing
    simpa [FlowDecomposition.decodedFlow,FlowDecomposition.matrixFlow] using aggregate_nonedge entries u v missing
  have balance : ∀ v,(∑ u,FlowDecomposition.decodedFlow (Equiv.refl _) (aggregate entries).value v u)-
      (∑ u,FlowDecomposition.decodedFlow (Equiv.refl _) (aggregate entries).value u v)=
      (if s=v then 1 else 0)-(if t=v then 1 else 0) := by
    intro v
    simpa [FlowDecomposition.decodedFlow,FlowDecomposition.matrixFlow] using aggregate_balance entries unit v
  obtain ⟨output,found,positive,mass,dominated,support⟩ :=
    FlowDecomposition.decompose_correct input.graph (Equiv.refl _) (aggregate entries).value s t nonnegative nonedge balance
  refine ⟨output,?_,positive,mass,?_,support⟩
  · simpa [compress] using found
  · simpa [FlowDecomposition.decodedFlow,FlowDecomposition.matrixFlow] using dominated

def compressCount (n k : ℕ) := n*(n*(k*(14*n+3)+5)+3)+1+(n*n+1)*FlowExtract.stepBudget n+6

theorem compress_count {s t : Fin n} (entries : FlowDecomposition.WeightedPaths input.graph s t) :
    (compress input entries).events.length ≤ compressCount n entries.length := by
  have first := aggregate_count entries
  have last := FlowExtract.decompose_count input (aggregate entries).value s t
  simp only [compress,List.length_append]
  dsimp[compressCount]
  omega

def compressWords (n k L : ℕ) := aggregateWords n k L+FlowExtract.decompositionWords n (cellBits n k L)

theorem compress_words {s t : Fin n} (entries : FlowDecomposition.WeightedPaths input.graph s t)
    (nonneg : ∀ e∈entries,0 ≤ e.1) (unit : (entries.map Prod.fst).sum=1)
    (L : ℕ) (constant : 3 ≤ L) (bits : ∀ e∈entries,(Code.ofRat e.1).bits ≤ L) :
    WordsWithin (compressWords n entries.length L) (compress input entries).events := by
  have cells (u v : Fin n) : (Code.ofRat (aggregate entries).value[u.val][v.val]).bits ≤ cellBits n entries.length L := by
    simpa [aggregate,Weights.materialize_get] using cell_bits entries u v L constant bits
  have last := FlowExtract.decompose_words input (aggregate entries).value s t _ cells
    (by intro u v;simpa using aggregate_nonneg entries nonneg u v)
    (by intro u v;simpa using aggregate_le_one entries nonneg unit u v)
    (by intro u v missing;simpa using aggregate_nonedge entries u v missing)
    (by intro v;simpa using aggregate_balance entries unit v)
  exact (wordsWithin_append _ _ _).mpr
    ⟨(aggregate_words entries L constant bits).mono (by dsimp[compressWords];omega),
      last.mono (by dsimp[compressWords];omega)⟩

 theorem compress_output_bits {s t : Fin n} (entries output : FlowDecomposition.WeightedPaths input.graph s t)
    (nonneg : ∀ e∈entries,0 ≤ e.1) (unit : (entries.map Prod.fst).sum=1)
    (returned : (compress input entries).value=some output)
    (L : ℕ) (constant : 3 ≤ L) (bits : ∀ e∈entries,(Code.ofRat e.1).bits ≤ L) :
    ∀ e∈output,(Code.ofRat e.1).bits ≤ 2*n*n*cellBits n entries.length L+4 := by
  obtain ⟨result,found,_,_,_,_,encoded⟩ := FlowDecomposition.decompose_encoding input.graph
    (Equiv.refl _) (aggregate entries).value s t
    (by intro u v;simpa [FlowDecomposition.decodedFlow,FlowDecomposition.matrixFlow] using aggregate_nonneg entries nonneg u v)
    (by intro u v missing;simpa [FlowDecomposition.decodedFlow,FlowDecomposition.matrixFlow] using aggregate_nonedge entries u v missing)
    (by intro v;simpa [FlowDecomposition.decodedFlow,FlowDecomposition.matrixFlow] using aggregate_balance entries unit v)
  have same : result=output := Option.some.inj (found.symm.trans (by simpa[compress] using returned))
  subst result
  have cells (u v : Fin n) : (Code.ofRat (aggregate entries).value[u.val][v.val]).bits ≤ cellBits n entries.length L := by
    simpa [aggregate,Weights.materialize_get] using cell_bits entries u v L constant bits
  have bound := FlowExtract.denominatorBits_bound (aggregate entries).value (cellBits n entries.length L) cells
  intro e mem
  have outputBound := (encoded e mem).2.2
  nlinarith

variable {h : ℕ} (source target : Fin h → Fin n)

def request (entries : List (Entry (G:=input.graph) source target)) (i : Fin h) :
    Traced (Option (FlowDecomposition.WeightedPaths input.graph (source i) (target i))) :=
  let selected := select source target i entries
  let output := compress input selected.value
  ⟨output.value,selected.events++output.events⟩

@[simp] theorem request_value (entries : List (Entry (G:=input.graph) source target)) (i : Fin h) :
    (request input source target entries i).value=
      (compress input (selectPaths source target entries i)).value := by simp[request]

 theorem request_count (entries : List (Entry (G:=input.graph) source target)) (i : Fin h) :
    (request input source target entries i).events.length ≤ 5*entries.length+1+compressCount n entries.length := by
  have first := select_count source target i entries
  have last := compress_count input (select source target i entries).value
  have length := selectPaths_length source target entries i
  simp only [select_value] at last
  simp only [request,List.length_append,select_value]
  apply Nat.add_le_add first
  apply last.trans
  unfold compressCount
  gcongr

 theorem request_words (entries : List (Entry (G:=input.graph) source target)) (i : Fin h)
    (nonneg : ∀ e∈entries,0 ≤ e.2.1)
    (unit : ((selectPaths source target entries i).map Prod.fst).sum=1)
    (L : ℕ) (constant : 3 ≤ L) (bits : ∀ e∈entries,(Code.ofRat e.2.1).bits ≤ L) :
    WordsWithin (n+h+L+1+compressWords n entries.length L) (request input source target entries i).events := by
  have first := select_words source target i entries L bits
  have last := compress_words input (selectPaths source target entries i)
    (selectPaths_nonneg source target entries nonneg i) unit L constant (selected_bits source target i entries L bits)
  have length := selectPaths_length source target entries i
  apply (wordsWithin_append _ _ _).mpr
  constructor
  · exact first.mono (by omega)
  · simp only [select_value]
    apply last.mono
    apply Nat.le_trans _ (Nat.le_add_left _ _)
    unfold compressWords aggregateWords cellWords cellBits FlowExtract.decompositionWords
    gcongr

end BuyAtBulk.Computation.Runtime.SparseSupplied
