import BuyAtBulk.Computation.Runtime.OriginalStoredOutput
import BuyAtBulk.Computation.Runtime.OriginalPreparedOptimization
import BuyAtBulk.Computation.Runtime.StoredCompactRounding

/-! Actual stored compact rounding is projected back to original typed paths
and original paid resource flags. All inputs are the cached finite arrays. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace BuyAtBulk.Computation.Runtime.Original
open BuyAtBulk.NodeReduction BuyAtBulk.Computation.StoredOriginal BuyAtBulk.UpperBound
open scoped BuyAtBulk.Computation.NodeReduction
open Rational
variable {n resources requests : ℕ} (tables : Tables n resources requests)
variable (prepared : CachedBuffers tables) (computed : prepared=(cachedBuffers tables).value)

def outputBuying (output : StoredOriginalOutput tables) : ℚ :=
  ∑ a : Fin resources,if output.bought[a.val] then tables.buying[a.val] else 0

def outputRental (output : StoredOriginalOutput tables) : ℚ :=
  (output.routes.map fun e=>tables.demand[e.1.val]*OriginalPipeline.pathResourceCost tables.graphData tables.graphData.length e.1 e.2).sum

def roundPrepared (point : Vector ℚ (PolynomialLP.CompactEncoding.variableCount prepared.count requests)) :
    Traced (Option (StoredOriginalOutput tables)) :=
  let native := StoredCompactRounding.run prepared.graphInput (prepared.data tables) point
  match native.value with
  | none=>⟨none,native.events++[⟨.branch,[1]⟩,⟨.write,[1]⟩]⟩
  | some output=>
    let projected := storedOutput tables prepared computed output.bought output.routes
    ⟨some projected.value,native.events++[⟨.branch,[1]⟩]++projected.events++[⟨.write,[1]⟩]⟩

theorem roundPrepared_correct (f : CompactFlow.Solution prepared.graphInput.graph requests)
    (same : PolynomialLP.CompactEncoding.Matches (prepared.data tables) f)
    (point : Vector ℚ (PolynomialLP.CompactEncoding.variableCount prepared.count requests))
    (coordinates : f.coordinates=PolynomialLP.CompactEncoding.decode (fun j=>point[j.val])) :
    ∃ output,(roundPrepared tables prepared computed point).value=some output ∧
      (outputBuying tables output : ℝ) ≤
        500000*Statements.buyingFactor requests (Optimization.scaleRatio requests) (Optimization.r requests)*f.buyingBudget ∧
      (outputRental tables output : ℝ) ≤
        500000*((Optimization.r requests : ℝ)*Statements.gridLevels requests (Optimization.scaleRatio requests))*f.rentalBudget ∧
      (output.routes.map fun e=>e.1).Perm (List.finRange requests) ∧
      ∀ e∈output.routes,∀ a,OriginalPipeline.usesResource tables.graphData e.1 e.2 a=true → output.bought[a.val]=true := by
  obtain ⟨native,returned,buying,rental,indices,support⟩ := StoredCompactRounding.run_correct prepared.graphInput (prepared.data tables) f same point coordinates
  let projected := (storedOutput tables prepared computed native.bought native.routes).value
  refine ⟨projected,?_,?_,?_,?_,?_⟩
  · simp only [roundPrepared,returned,projected]
  · have exactCost : outputBuying tables projected=
        nodeBuying (fun v=>prepared.buying[v.val]) (StoredState.boughtSet native.bought) := by
      rw [outputBuying,storedOutput_buying]
      simp only [nodeBuying,StoredState.mem_boughtSet]
    rw [exactCost]
    exact buying
  · have exactCost : outputRental tables projected=
        Rounding.rentalCost (fun v=>prepared.physical[v.val]) (fun i=>prepared.demand[i.val]) native.routes := by
      rw [outputRental,storedOutput_rental,Rounding.rentalCost_eq]
      rfl
    rw [exactCost]
    exact rental
  · change ((storedRoutes tables prepared computed native.routes).value.map fun e=>e.1).Perm _
    rw [storedRoutes_value,List.map_map]
    exact indices
  · exact storedOutput_supported tables prepared computed native.bought native.routes support

def roundPreparedCount (r h m : ℕ) := StoredCompactRounding.countBudget m h+r*(27*m+9)+
  ((14*(m+1)+17)*(m+1)+14)*h+5

theorem roundPrepared_count (f : CompactFlow.Solution prepared.graphInput.graph requests)
    (same : PolynomialLP.CompactEncoding.Matches (prepared.data tables) f)
    (point : Vector ℚ (PolynomialLP.CompactEncoding.variableCount prepared.count requests))
    (coordinates : f.coordinates=PolynomialLP.CompactEncoding.decode (fun j=>point[j.val])) :
    (roundPrepared tables prepared computed point).events.length ≤ roundPreparedCount resources requests prepared.count := by
  have nativeCount := StoredCompactRounding.run_count prepared.graphInput (prepared.data tables) f same point coordinates
  obtain ⟨native,returned,_,_,indices,_⟩ := StoredCompactRounding.run_correct prepared.graphInput (prepared.data tables) f same point coordinates
  have projected := storedOutput_count tables prepared computed native.bought native.routes
  have length : native.routes.length=requests := by
    have sameLength := indices.length_eq
    simpa only [List.length_map,List.length_finRange] using sameLength
  rw [length] at projected
  unfold roundPrepared
  dsimp only
  rw [returned]
  simp only [List.length_append,List.length_cons,List.length_nil]
  dsimp only [roundPreparedCount]
  omega

def roundPreparedWords (n r h m L : ℕ) := StoredCompactRounding.wordBudget m h L+n+r+h+m+20

theorem roundPrepared_words (f : CompactFlow.Solution prepared.graphInput.graph requests)
    (same : PolynomialLP.CompactEncoding.Matches (prepared.data tables) f)
    (point : Vector ℚ (PolynomialLP.CompactEncoding.variableCount prepared.count requests))
    (coordinates : f.coordinates=PolynomialLP.CompactEncoding.decode (fun j=>point[j.val]))
    (L : ℕ) (constant : 5 ≤ L)
    (pointBits : ∀ j : Fin (PolynomialLP.CompactEncoding.variableCount prepared.count requests),(Code.ofRat point[j.val]).bits+1 ≤ L)
    (buyingBits : ∀ v : Fin prepared.count,(Code.ofRat prepared.buying[v.val]).bits+1 ≤ L)
    (physicalBits : ∀ v : Fin prepared.count,(Code.ofRat prepared.physical[v.val]).bits+1 ≤ L) :
    WordsWithin (roundPreparedWords n resources requests prepared.count L)
      (roundPrepared tables prepared computed point).events := by
  let K := roundPreparedWords n resources requests prepared.count L
  have native := (StoredCompactRounding.run_words prepared.graphInput (prepared.data tables) f same point coordinates L constant pointBits buyingBits physicalBits).mono
    (show _ ≤ K by dsimp[K,roundPreparedWords];omega)
  have one : 1 ≤ K := by dsimp[K,roundPreparedWords];omega
  change WordsWithin K (roundPrepared tables prepared computed point).events
  unfold roundPrepared
  dsimp only
  split
  · simp_all [wordsWithin_append,wordsWithin_cons]
  · rename_i output returned
    have projected := storedOutput_words tables prepared computed output.bought output.routes K
      (by dsimp[K,roundPreparedWords];omega)
    simp_all [wordsWithin_append,wordsWithin_cons]

end BuyAtBulk.Computation.Runtime.Original
