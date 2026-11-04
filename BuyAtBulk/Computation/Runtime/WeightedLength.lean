import BuyAtBulk.Computation.Runtime.RouteQuery
import BuyAtBulk.Computation.Runtime.OriginalNumeric
import BuyAtBulk.Computation.FlowDecomposition.Algorithm

/-! Finite weighted length metadata traverses the actual returned simple paths.
Both each path sum and the outer weighted sum use normalized rational primitives. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace BuyAtBulk.Computation.Runtime.WeightedLength
open Rational
variable {n : ℕ} {G : SimpleGraph (Fin n)} {s t : Fin n}

def terms (physical : Vector ℚ n) : FlowDecomposition.WeightedPaths G s t → Traced (List ℚ)
  | [] => ⟨[],[⟨.branch,[1]⟩]⟩
  | entry::rest =>
    let length := Queries.cost physical entry.2.val
    let product := ratMul entry.1 length.value
    let tail := terms physical rest
    ⟨product.value::tail.value,
      [⟨.branch,[1]⟩,⟨.scan,[1]⟩,⟨.read,[(Code.ofRat entry.1).bits]⟩]++length.events++product.events++tail.events++
        [⟨.cons,[(Code.ofRat product.value).bits]⟩]⟩

@[simp] theorem terms_value (physical : Vector ℚ n) (entries : FlowDecomposition.WeightedPaths G s t) :
    (terms physical entries).value=entries.map (fun e=>e.1*ShortestPath.traversalCost G (fun v=>physical[v.val]) e.2.val) := by
  induction entries <;> simp_all [terms]

theorem terms_count (physical : Vector ℚ n) (entries : FlowDecomposition.WeightedPaths G s t) :
    (terms physical entries).events.length ≤ (4*n+10)*entries.length+1 := by
  induction entries with
  | nil => simp [terms]
  | cons entry rest ih =>
    have path := Queries.cost_count physical entry.2.val
    have size := entry.2.property.length_lt
    simp only [Fintype.card_fin] at size
    simp only [terms,List.length_append,List.length_cons,List.length_nil,ratMul_length]
    nlinarith

def run (physical : Vector ℚ n) (entries : FlowDecomposition.WeightedPaths G s t) : Traced ℚ :=
  let values := terms physical entries
  let sum := Original.ratSum values.value
  ⟨sum.value,values.events++sum.events⟩

@[simp] theorem run_value (physical : Vector ℚ n) (entries : FlowDecomposition.WeightedPaths G s t) :
    (run physical entries).value=(entries.map (fun e=>e.1*ShortestPath.traversalCost G (fun v=>physical[v.val]) e.2.val)).sum := by
  simp only [run,Original.ratSum_value,terms_value]

theorem run_count (physical : Vector ℚ n) (entries : FlowDecomposition.WeightedPaths G s t) :
    (run physical entries).events.length ≤ (4*n+16)*entries.length+3 := by
  have inputs := terms_count physical entries
  simp only [run,List.length_append,Original.ratSum_count,terms_value,List.length_map]
  nlinarith

def productBudget (n L W : ℕ) := 2*(W+Runtime.ShortestPath.labelBudget n L)+8

theorem product_bits (physical : Vector ℚ n) (entry : ℚ×G.Path s t) (L W : ℕ) (constant : 5 ≤ L)
    (physicalBits : ∀ v : Fin n,(Code.ofRat physical[v.val]).bits+1 ≤ L)
    (weightBits : (Code.ofRat entry.1).bits ≤ W) :
    (Code.ofRat (entry.1*(Queries.cost physical entry.2.val).value)).bits ≤ productBudget n L W := by
  have length := Queries.cost_bits physical entry.2.val n L constant
    (by have size:=entry.2.property.length_lt;simpa using size.le) physicalBits
  have result := ratMul_result_bits entry.1 (Queries.cost physical entry.2.val).value
  dsimp only [productBudget]
  omega

def wordBudget (n k L W : ℕ) :=
  n+L+W+2*(L+Runtime.ShortestPath.labelBudget n L)+10+(8*k+6)*(productBudget n L W+6)+12

theorem terms_bits (physical : Vector ℚ n) (entries : FlowDecomposition.WeightedPaths G s t)
    (L W : ℕ) (constant : 5 ≤ L)
    (physicalBits : ∀ v : Fin n,(Code.ofRat physical[v.val]).bits+1 ≤ L)
    (weightBits : ∀ e∈entries,(Code.ofRat e.1).bits ≤ W) :
    ∀ q∈(terms physical entries).value,(Code.ofRat q).bits ≤ productBudget n L W := by
  intro q member
  rw [terms_value] at member
  obtain ⟨entry,mem,rfl⟩ := List.mem_map.mp member
  simpa only [Queries.cost_value] using product_bits physical entry L W constant physicalBits (weightBits entry mem)

theorem terms_words (physical : Vector ℚ n) (entries : FlowDecomposition.WeightedPaths G s t)
    (L W K : ℕ) (constant : 5 ≤ L)
    (physicalBits : ∀ v : Fin n,(Code.ofRat physical[v.val]).bits+1 ≤ L)
    (weightBits : ∀ e∈entries,(Code.ofRat e.1).bits ≤ W)
    (indices : n ≤ K) (budget : L+W+2*(L+Runtime.ShortestPath.labelBudget n L)+productBudget n L W+10 ≤ K) :
    WordsWithin K (terms physical entries).events := by
  have one : 1 ≤ K := by omega
  induction entries with
  | nil => simp [terms,WordsWithin,one]
  | cons entry rest ih =>
    have weight := weightBits entry (by simp)
    have pathSize : entry.2.val.length ≤ n := by have size:=entry.2.property.length_lt;simpa using size.le
    have path := Queries.cost_words physical entry.2.val n L K constant pathSize physicalBits indices (by omega)
    have length := Queries.cost_bits physical entry.2.val n L constant pathSize physicalBits
    have product : WordsWithin K (ratMul entry.1 (Queries.cost physical entry.2.val).value).events := by
      intro event member word present
      exact (ratMul_words _ _ event member word present).trans (by dsimp [productBudget] at budget;omega)
    have output := product_bits physical entry L W constant physicalBits weight
    have tail := ih (fun e mem=>weightBits e (by simp[mem]))
    simp_all [terms,wordsWithin_append,wordsWithin_cons] <;> omega

theorem run_words (physical : Vector ℚ n) (entries : FlowDecomposition.WeightedPaths G s t)
    (L W : ℕ) (constant : 5 ≤ L)
    (physicalBits : ∀ v : Fin n,(Code.ofRat physical[v.val]).bits+1 ≤ L)
    (weightBits : ∀ e∈entries,(Code.ofRat e.1).bits ≤ W) :
    WordsWithin (wordBudget n entries.length L W) (run physical entries).events := by
  have values := terms_words physical entries L W (wordBudget n entries.length L W) constant physicalBits weightBits
    (by dsimp[wordBudget];omega) (by dsimp[wordBudget,productBudget];nlinarith)
  have product := terms_bits physical entries L W constant physicalBits weightBits
  have sum := (Original.ratSum_general_words (terms physical entries).value (productBudget n L W+6)
    (by omega) (by intro q mem;have bits:=product q mem;omega)).mono
    (show _ ≤ wordBudget n entries.length L W by
      simp only [terms_value,List.length_map]
      dsimp[wordBudget];omega)
  exact (wordsWithin_append _ _ _).mpr ⟨values,sum⟩

def outputBudget (n k L W : ℕ) := 2*(2*k+1)*(productBudget n L W+6)+2

theorem run_bits (physical : Vector ℚ n) (entries : FlowDecomposition.WeightedPaths G s t)
    (L W : ℕ) (constant : 5 ≤ L)
    (physicalBits : ∀ v : Fin n,(Code.ofRat physical[v.val]).bits+1 ≤ L)
    (weightBits : ∀ e∈entries,(Code.ofRat e.1).bits ≤ W) :
    (Code.ofRat (run physical entries).value).bits ≤ outputBudget n entries.length L W := by
  have products := terms_bits physical entries L W constant physicalBits weightBits
  have sum := HelperExpressions.sum_rat_bits (terms physical entries).value (productBudget n L W+6)
    (by omega) (by intro q mem;have bound:=products q mem;omega)
  simpa only [run,Original.ratSum_value,terms_value,List.length_map,outputBudget] using sum

end BuyAtBulk.Computation.Runtime.WeightedLength
