import BuyAtBulk.Computation.Runtime.CoreInitialization
import BuyAtBulk.Computation.Runtime.CoreRequestOrder
import BuyAtBulk.Computation.Runtime.BatchWords

/-! Closed post-helper core execution. Inputs are stored vectors and a
materialized helper node list; the complete helper constructor composes here. -/
namespace BuyAtBulk.Computation.Runtime.StoredCore
open BuyAtBulk.UpperBound
open Rational
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

def thresholdFactor (r : ℕ) : Traced ℚ := do
  let parameter ← ratCast r
  let product ← ratMul 6 parameter
  ratAdd product 6

@[simp] theorem thresholdFactor_value (r : ℕ) : (thresholdFactor r).value=6*(r : ℚ)+6 := rfl
@[simp] theorem thresholdFactor_count (r : ℕ) : (thresholdFactor r).events.length=5 := rfl

def coreInputBudget (L : ℕ) := 16*L+128

theorem thresholdFactor_runtime (r L : ℕ) (input_width : r.size ≤ L) :
    WordsWithin (coreInputBudget L) (thresholdFactor r).events ∧
      (Code.ofRat (thresholdFactor r).value).bits ≤ coreInputBudget L := by
  have literal : (Code.ofRat 6).bits=6 := by decide
  have cast_width : (Code.ofRat (r : ℚ)).bits ≤ L+3 := by rw[SourceCoefficients.natCast_bits];omega
  have mul_width : (Code.ofRat (6*(r : ℚ))).bits ≤ 2*L+26 := by
    have actual := ratMul_result_bits 6 (r : ℚ)
    rw[literal] at actual
    omega
  have add_width : (Code.ofRat (6*(r : ℚ)+6)).bits ≤ 4*L+72 := by
    have actual := ratAdd_result_bits (6*(r : ℚ)) 6
    rw[literal] at actual
    omega
  have mul_trace : WordsWithin (coreInputBudget L) (ratMul 6 (r : ℚ)).events := by
    intro event member word present
    have actual := ratMul_words 6 (r : ℚ) event member word present
    rw[literal] at actual
    unfold coreInputBudget
    omega
  have add_trace : WordsWithin (coreInputBudget L) (ratAdd (6*(r : ℚ)) 6).events := by
    intro event member word present
    have actual := ratAdd_words (6*(r : ℚ)) 6 event member word present
    rw[literal] at actual
    unfold coreInputBudget
    omega
  constructor
  · simp only[thresholdFactor,Traced.bind_events,Traced.bind_value,ratCast,emit_value,ratMul_value,
      wordsWithin_append,emit,wordsWithin_cons,wordsWithin_nil,List.mem_singleton,forall_eq,and_true]
    exact ⟨by unfold coreInputBudget;omega,mul_trace,add_trace⟩
  · exact add_width.trans (by unfold coreInputBudget;omega)

def execute (buying physical : Vector ℚ n) (budget : ℚ) (allowance : Vector ℚ h)
    (source target : Vector (Fin n) h) (active : Vector Bool h) (ratio r : ℕ)
    (seed : Vector Bool n) (helperNodes : List (Fin n)) :
    Traced (Option (StoredState.State input.graph × List (StoredBatch.Entry input source target))) := do
  let initial ← initialState input buying seed helperNodes
  let order ← requestOrder active allowance
  let factor ← thresholdFactor r
  StoredBatch.run input buying physical budget ratio factor source target allowance order initial

theorem execute_value (buying physical : Vector ℚ n) (budget : ℚ) (allowance : Vector ℚ h)
    (source target : Vector (Fin n) h) (active : Vector Bool h) (ratio r : ℕ)
    (seed : Vector Bool n) (helperNodes : List (Fin n)) (ratio_ge : 2 ≤ ratio) :
    StoredBatch.decodeOption input source target (execute input buying physical budget allowance source target active ratio r seed helperNodes).value=
      Computation.Batch.run input.graph (Equiv.refl _) (fun v => buying[v.val]) (fun v => physical[v.val]) budget ratio (6*(r : ℚ)+6)
        (fun i => source[i.val]) (fun i => target[i.val]) (fun i => allowance[i.val])
        (CoreRun.requestOrder (StoredState.boughtSet active) (fun i => allowance[i.val]))
        {bought:=StoredState.boughtSet seed∪helperNodes.toFinset∪Core.zeroBuyingNodes (Equiv.refl _) (fun v => buying[v.val]),centers:=[],edges:=[]} := by
  simp only[execute,Traced.bind_value,thresholdFactor_value]
  rw[StoredBatch.run_value (ratio_ge := ratio_ge),initialState_value,requestOrder_value]

def executionCount (n h k : ℕ) := k*(4*n+3)+6*n+4+requestOrderCount h+5+
  h*(StoredServe.serveBudget n h (4*h)+10)+2

theorem execute_count (buying physical : Vector ℚ n) (budget : ℚ) (allowance : Vector ℚ h)
    (source target : Vector (Fin n) h) (active : Vector Bool h) (ratio r : ℕ)
    (seed : Vector Bool n) (nodes : List (Fin n)) (ratio_ge : 2 ≤ ratio) :
    (execute input buying physical budget allowance source target active ratio r seed nodes).events.length ≤ executionCount n h nodes.length := by
  have initial := initialState_count input buying seed nodes
  have order := requestOrder_count active allowance
  have order_length := requestOrder_length active allowance
  have batch := StoredBatch.run_count input buying physical budget ratio (thresholdFactor r).value source target allowance
    (requestOrder active allowance).value (initialState input buying seed nodes).value ratio_ge
  have initial_centers : (initialState input buying seed nodes).value.centers.length=0 := rfl
  rw[initial_centers] at batch
  simp only[StoredBatch.countBudget,Nat.zero_add] at batch
  have monotone := StoredBatch.serveBudget_mono (n:=n) (h:=h) (Nat.mul_le_mul_left 4 order_length)
  have product := Nat.mul_le_mul order_length (Nat.add_le_add_right monotone 10)
  simp only[execute,Traced.bind_events,Traced.bind_value,List.length_append,thresholdFactor_count]
  unfold executionCount
  omega

def executionWords (n h L : ℕ) := StoredBatch.wordBudget n h (coreInputBudget L)+n+h+16*L+256

theorem execute_words (buying physical : Vector ℚ n) (budget : ℚ) (allowance : Vector ℚ h)
    (source target : Vector (Fin n) h) (active : Vector Bool h) (ratio r : ℕ)
    (seed : Vector Bool n) (nodes : List (Fin n)) (L : ℕ) (constant : 8 ≤ L) (ratio_ge : 2 ≤ ratio)
    (buying_width : ∀ v : Fin n, (Code.ofRat buying[v.val]).bits ≤ L)
    (physical_width : ∀ v : Fin n, (Code.ofRat physical[v.val]).bits ≤ L)
    (budget_width : (Code.ofRat budget).bits ≤ L) (allowance_width : ∀ i : Fin h, (Code.ofRat allowance[i.val]).bits ≤ L)
    (ratio_width : ratio.size ≤ L) (r_width : r.size ≤ L) :
    WordsWithin (executionWords n h L) (execute input buying physical budget allowance source target active ratio r seed nodes).events := by
  let K := executionWords n h L
  let S := coreInputBudget L
  have LS : L ≤ S := by dsimp[S,coreInputBudget];omega
  have initial := (initialState_words input buying seed nodes L buying_width).mono
    (show n+L+5 ≤ K by dsimp[K,executionWords];omega)
  have order := (requestOrder_words active allowance L allowance_width).mono
    (show 2*h+L+5 ≤ K by dsimp[K,executionWords,StoredBatch.wordBudget];omega)
  have threshold := (thresholdFactor_runtime r L r_width).1.mono (show coreInputBudget L ≤ K by dsimp[K,executionWords,coreInputBudget];omega)
  have batch := (StoredBatch.run_words input buying physical budget ratio (thresholdFactor r).value source target allowance
    (requestOrder active allowance).value (initialState input buying seed nodes).value S (by dsimp[S,coreInputBudget];omega) ratio_ge
    (fun v => (buying_width v).trans LS) (fun v => (physical_width v).trans LS) (budget_width.trans LS)
    (fun i => (allowance_width i).trans LS) (thresholdFactor_runtime r L r_width).2 (ratio_width.trans LS)
    (by simp[initialState,StoredAttachment.Metadata])).mono
    (show StoredBatch.wordBudget n h S ≤ K by dsimp[K,executionWords,S];omega)
  simpa only[execute,Traced.bind_events,Traced.bind_value,wordsWithin_append] using
    And.intro initial (And.intro order (And.intro threshold batch))

end BuyAtBulk.Computation.Runtime.StoredCore
