import BuyAtBulk.Computation.Runtime.CompactFieldsMatches
import BuyAtBulk.Computation.Runtime.OptimizedCorrectness

/-! Closed native compact rounding: the only LP input is its actual stored
optimizer vector. Decomposition, metadata and optimized rounding are computed. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.Computation.Runtime.StoredCompactRounding
open Rational BuyAtBulk.PolynomialLP.CompactEncoding BuyAtBulk.UpperBound
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

def run (data : Data n h) (point : Vector ℚ (variableCount n h)) :
    Traced (Option (StoredRounding.Output input data.source data.target)) :=
  let fields := CompactLift.prepare input data.buying data.physical data.source data.target point
  match fields.value with
  | none=>⟨none,fields.events++[⟨.branch,[1]⟩,⟨.write,[1]⟩]⟩
  | some values=>
    let output := StoredRounding.optimized input data.buying data.physical values.opening values.budget data.source data.target values.allowance
    ⟨output.value,fields.events++[⟨.branch,[1]⟩]++output.events++[⟨.write,[1]⟩]⟩

theorem run_correct (data : Data n h) (f : CompactFlow.Solution input.graph h) (same : Matches data f)
    (point : Vector ℚ (variableCount n h)) (coordinates : f.coordinates=decode (fun j=>point[j.val])) :
    ∃ output,(run input data point).value=some output ∧
      (nodeBuying (fun v=>data.buying[v.val]) (StoredState.boughtSet output.bought) : ℝ) ≤
        500000*Statements.buyingFactor h (Optimization.scaleRatio h) (Optimization.r h)*f.buyingBudget ∧
      (Rounding.rentalCost (fun v=>data.physical[v.val]) (fun i=>data.demand[i.val]) output.routes : ℝ) ≤
        500000*((Optimization.r h : ℝ)*Statements.gridLevels h (Optimization.scaleRatio h))*f.rentalBudget ∧
      (output.routes.map fun e=>e.1).Perm (List.finRange h) ∧
      ∀ e∈output.routes,∀ v∈e.2.val.support,output.bought[v.val]=true := by
  obtain ⟨fields,computed,correct⟩ := CompactLift.prepare_correct input data f same point coordinates
  let lp := FlowDecomposition.toNodeLP input.graph (Equiv.refl _) f
  obtain ⟨output,returned,buying,rental,indices,support⟩ := StoredRounding.optimized_correct input lp
    data.buying data.physical fields.opening fields.budget data.source data.target fields.allowance
    (funext fun i=>(same.source i).symm) (funext fun i=>(same.target i).symm)
    (funext fun v=>(same.buying v).symm) (funext fun v=>(same.physical v).symm)
    (funext fun v=>(correct.opening v).symm) correct.budget correct.allowance
  refine ⟨output,?_,?_,?_,indices,?_⟩
  · simp only [run,computed,returned]
  · simpa only [correct.budget] using buying
  · have demand : lp.demand=fun i=>data.demand[i.val] := funext fun i=>(same.demand i).symm
    rw [demand] at rental
    have budget : (lp.rentalBudget : ℝ) ≤ f.rentalBudget := by
      exact_mod_cast FlowDecomposition.toNodeLP_rentalBudget_le input.graph (Equiv.refl _) f
    exact rental.trans (mul_le_mul_of_nonneg_left budget (by positivity))
  · intro e member v present
    exact (StoredState.mem_boughtSet output.bought v).mp
      ((support e member).1 (List.mem_toFinset.mpr present))

def countBudget (n h : ℕ) := CompactLift.prepareCount n h+StoredRounding.optimizedCount n h+2

theorem run_count (data : Data n h) (f : CompactFlow.Solution input.graph h) (same : Matches data f)
    (point : Vector ℚ (variableCount n h)) (coordinates : f.coordinates=decode (fun j=>point[j.val])) :
    (run input data point).events.length ≤ countBudget n h := by
  have fields := CompactLift.prepare_matches_count input data f same point coordinates
  unfold run
  dsimp only
  split
  · simp only [List.length_append,List.length_cons,List.length_nil]
    dsimp[countBudget]
    omega
  · rename_i values found
    have rounded := StoredRounding.optimized_count input data.buying data.physical values.opening values.budget data.source data.target values.allowance
    simp only [List.length_append,List.length_cons,List.length_nil]
    dsimp[countBudget]
    omega

def roundingLeafBudget (n L : ℕ) := L+CompactLift.budgetBits n L+CompactLift.allowanceBits n L+10

def wordBudget (n h L : ℕ) := CompactLift.prepareWords n h L+StoredRounding.optimizedWords n h (roundingLeafBudget n L)+10

theorem run_words (data : Data n h) (f : CompactFlow.Solution input.graph h) (same : Matches data f)
    (point : Vector ℚ (variableCount n h)) (coordinates : f.coordinates=decode (fun j=>point[j.val]))
    (L : ℕ) (constant : 5 ≤ L)
    (pointBits : ∀ j : Fin (variableCount n h),(Code.ofRat point[j.val]).bits+1 ≤ L)
    (buyingBits : ∀ v : Fin n,(Code.ofRat data.buying[v.val]).bits+1 ≤ L)
    (physicalBits : ∀ v : Fin n,(Code.ofRat data.physical[v.val]).bits+1 ≤ L) :
    WordsWithin (wordBudget n h L) (run input data point).events := by
  let K := wordBudget n h L
  let S := roundingLeafBudget n L
  have fields := (CompactLift.prepare_matches_words input data f same point coordinates L constant pointBits buyingBits physicalBits).mono
    (show _ ≤ K by dsimp[K,wordBudget];omega)
  have one : 1 ≤ K := by dsimp[K,wordBudget];omega
  change WordsWithin K (run input data point).events
  unfold run
  dsimp only
  split
  · simp_all [wordsWithin_append,wordsWithin_cons] <;> aesop
  · rename_i values found
    have bounds := CompactLift.prepare_matches_field_bits input data f same point coordinates values found L constant pointBits buyingBits physicalBits
    have rounded := (StoredRounding.optimized_words input data.buying data.physical values.opening values.budget data.source data.target values.allowance S
      (by dsimp[S,roundingLeafBudget];omega)
      (fun v=>(Nat.le_add_right _ 1).trans (buyingBits v) |>.trans (by dsimp[S,roundingLeafBudget];omega))
      (fun v=>(Nat.le_add_right _ 1).trans (physicalBits v) |>.trans (by dsimp[S,roundingLeafBudget];omega))
      (fun v=>(Nat.le_add_right _ 1).trans (bounds.1 v) |>.trans (by dsimp[S,roundingLeafBudget];omega))
      (bounds.2.1.trans (by dsimp[S,roundingLeafBudget];omega))
      (fun i=>(bounds.2.2 i).trans (by dsimp[S,roundingLeafBudget];omega))).mono
        (show _ ≤ K by dsimp[K,wordBudget,S];omega)
    simp_all [wordsWithin_append,wordsWithin_cons] <;> aesop

end BuyAtBulk.Computation.Runtime.StoredCompactRounding
