import BuyAtBulk.Computation.Runtime.SparseSuppliedRun
import BuyAtBulk.Computation.Runtime.SparseSuppliedOutput

/-! Standalone constructive sparsification of a supplied weighted-path list.
The stored output keeps openings unchanged and reduces every resource marginal. -/
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace BuyAtBulk.Computation.Runtime.SparseSupplied
open Rational StoredOriginal
variable {n resources h : ℕ} (tables : Tables n resources h)

def graphEncoding : ShortestPath.GraphEncoding n :=
  ⟨tables.adjacency,tables.symmetric,tables.loopless⟩

def storedRun (fractional : Fractional tables) : Traced (Option (List
    (Entry (G:=tables.graphData.graph) tables.graphData.source tables.graphData.target))) :=
  run tables.graphData.source tables.graphData.target (graphEncoding tables) fractional.entries

 theorem storedRun_correct (fractional : Fractional tables) (L : ℕ) (constant : 3 ≤ L)
    (bits : ∀ e∈fractional.entries,(Code.ofRat e.2.1).bits ≤ L) :
    ∃ output : Fractional tables,
      (storedRun tables fractional).value=some output.entries ∧
      output.opening=fractional.opening ∧ output.entries.length ≤ h*(n*n+1) ∧
      (∀ e∈output.entries,0<e.2.1) ∧
      OriginalPipeline.buyingBudget tables.graphData (output.decode tables)=
        OriginalPipeline.buyingBudget tables.graphData (fractional.decode tables) ∧
      (∀ i,OriginalPipeline.fractionalLength tables.graphData (output.decode tables) i ≤
        OriginalPipeline.fractionalLength tables.graphData (fractional.decode tables) i) ∧
      OriginalPipeline.rentalBudget tables.graphData (output.decode tables) ≤
        OriginalPipeline.rentalBudget tables.graphData (fractional.decode tables) ∧
      (∀ e∈output.entries,(Code.ofRat e.2.1).bits ≤ 2*n*n*cellBits n fractional.entries.length L+4) ∧
      (storedRun tables fractional).events.length ≤ runCount n fractional.entries.length h ∧
      WordsWithin (runWords n fractional.entries.length h L) (storedRun tables fractional).events := by
  have per (i : Fin h) := compress_correct (graphEncoding tables)
    (selectPaths tables.graphData.source tables.graphData.target fractional.entries i)
    (selectPaths_nonneg _ _ _ fractional.nonneg i) (fractional.unit i)
  choose paths returned positive mass dom support using per
  have requestReturned (i : Fin h) :
      (request (graphEncoding tables) tables.graphData.source tables.graphData.target fractional.entries i).value=
        some (paths i) := by rw [request_value];exact returned i
  have nonnegative : ∀ i e,e∈paths i → 0 ≤ e.1 := fun i e mem=>(positive i e mem).le
  let output := storedOfFamily tables fractional paths nonnegative mass dom
  refine ⟨output,?_,rfl,storedOfFamily_count _ _ _ _ _ _ support,?_,
    storedOfFamily_buying _ _ _ _ _ _,storedOfFamily_length _ _ _ _ _ _,
    storedOfFamily_rental _ _ _ _ _ _,?_,?_,?_⟩
  · exact runRequests_value _ _ _ _ paths requestReturned (List.finRange h)
  · intro e member
    obtain ⟨i,_,mem⟩ := List.mem_flatMap.mp member
    obtain ⟨p,present,rfl⟩ := List.mem_map.mp mem
    exact positive i p present
  · intro e member
    obtain ⟨i,_,mem⟩ := List.mem_flatMap.mp member
    obtain ⟨p,present,rfl⟩ := List.mem_map.mp mem
    have bound := compress_output_bits (graphEncoding tables)
      (selectPaths tables.graphData.source tables.graphData.target fractional.entries i) (paths i)
      (selectPaths_nonneg _ _ _ fractional.nonneg i) (fractional.unit i) (returned i)
      L constant (selected_bits _ _ i fractional.entries L bits) p present
    apply bound.trans
    have length := selectPaths_length tables.graphData.source tables.graphData.target fractional.entries i
    unfold cellBits
    gcongr
  · simpa only [storedRun,run,List.length_finRange] using runRequests_count _ _ _ _ paths requestReturned support (List.finRange h)
  · exact runRequests_words _ _ _ _ paths requestReturned fractional.nonneg fractional.unit L constant bits (List.finRange h)

end BuyAtBulk.Computation.Runtime.SparseSupplied
