import BuyAtBulk.Computation.Runtime.PositiveProjection
import BuyAtBulk.Computation.Runtime.CoreOutputBound

/-! Positive requests alone determine helper rows. Inactive slots use free
self-pairs; an empty positive phase returns its seed without a helper run. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace BuyAtBulk.Computation.Runtime.StoredRounding
open BuyAtBulk.UpperBound
open Rational
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

def positiveRun (buying physical opening : Vector ℚ n) (budget : ℚ)
    (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (ratio r : ℕ) (seed : Vector Bool n) (ratio_ge : 2 ≤ ratio) :
    Traced (Option (StoredState.State input.graph × List (StoredBatch.Entry input source target))) :=
  let active := activeFlags lengths true
  let empty := activeEmpty active.value
  let prefixEvents := active.events++empty.events++[⟨Operation.branch,[1]⟩]
  if empty.value then
    ⟨some (⟨seed,[],[]⟩,[]),prefixEvents++[({operation := Operation.cons, words := [n.size,h.size]} : Event)]⟩
  else
    let allowances := allowance lengths
    let dummy := zeroTarget target source lengths
    let answer := StoredCore.run input buying physical opening budget allowances.value source dummy.value active.value ratio r seed ratio_ge
    let converted : StoredResult input.graph (fun i : Fin h => source[i.val])
        (Rounding.positiveTarget (fun i => source[i.val]) (fun i => target[i.val]) (fun i => lengths[i.val])) := transportResult (G:=input.graph) rfl
      (show (fun i : Fin h => dummy.value[i.val]) = Rounding.positiveTarget
        (fun i => source[i.val]) (fun i => target[i.val]) (fun i => lengths[i.val]) from
        funext (zeroTarget_get target source lengths)) answer.value
    let events : List Event := prefixEvents++allowances.events++dummy.events++answer.events++[⟨.branch,[1]⟩]
    match converted with
    | none => ⟨none,events⟩
    | some (after,entries) =>
      let projected := projectPositiveEntries input source target lengths entries
      ⟨some (after,projected.value),events++projected.events++[({operation := Operation.cons, words := [n.size,h.size]} : Event)]⟩

theorem positiveRun_value (buying physical opening : Vector ℚ n) (budget : ℚ)
    (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (ratio r : ℕ) (seed : Vector Bool n) (ratio_ge : 2 ≤ ratio) :
    StoredBatch.decodeOption input source target
      (positiveRun input buying physical opening budget source target lengths ratio r seed ratio_ge).value =
      Rounding.positiveRun input.graph (Equiv.refl _) (fun v => buying[v.val]) (fun v => physical[v.val])
        (fun v => opening[v.val]) budget (fun i => source[i.val]) (fun i => target[i.val])
        (fun i => lengths[i.val]) ratio r (StoredState.boughtSet seed) := by
  have activeEq := activeFlags_positiveSet lengths
  simp only [positiveRun,Rounding.positiveRun,activeEmpty_value,activeEq,decide_eq_true_eq]
  split_ifs with empty
  · rfl
  · have equation := StoredCore.run_value input buying physical opening budget (allowance lengths).value source
      (zeroTarget target source lengths).value (activeFlags lengths true).value ratio r seed ratio_ge
    have transported := congrArg (transportSemantic (G:=input.graph) rfl
      (show (fun i : Fin h => (zeroTarget target source lengths).value[i.val]) = Rounding.positiveTarget
        (fun i => source[i.val]) (fun i => target[i.val]) (fun i => lengths[i.val]) from
        funext (zeroTarget_get target source lengths))) equation
    rw [core_transport] at transported
    simp only [activeFlags_positiveSet] at transported
    have allowEq : (fun i : Fin h => (allowance lengths).value[i.val])=Rounding.allowance (fun i => lengths[i.val]) :=
      funext (allowance_get lengths)
    rw [allowEq] at transported
    change transportSemantic _ _ (decodeResult _ _ _ _) = _ at transported
    rw [← decode_transport] at transported
    rw [← transported]
    generalize transportResult _ _ _ = result
    cases result with
    | none => rfl
    | some result =>
      rcases result with ⟨after,entries⟩
      simp only [decodeResult,StoredBatch.decodeOption,Option.map_some,projectPositiveEntries_value]


def positiveCount (n h : ℕ) := (5*h+1)+(7*h+2)+(7*h+1)+(6*h+1)+StoredCore.coreCount n h+7*h+10

theorem positiveRun_count (buying physical opening : Vector ℚ n) (budget : ℚ)
    (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (ratio r : ℕ) (seed : Vector Bool n) (ratio_ge : 2 ≤ ratio) :
    (positiveRun input buying physical opening budget source target lengths ratio r seed ratio_ge).events.length ≤ positiveCount n h := by
  have active := activeFlags_count lengths true
  have empty := activeEmpty_count (activeFlags lengths true).value
  have allowances := allowance_count lengths
  have dummy := zeroTarget_count target source lengths
  have core := StoredCore.run_count input buying physical opening budget (allowance lengths).value source
    (zeroTarget target source lengths).value (activeFlags lengths true).value ratio r seed ratio_ge
  have out := StoredCore.run_output_bound input buying physical opening budget (allowance lengths).value source
    (zeroTarget target source lengths).value (activeFlags lengths true).value ratio r seed ratio_ge
  simp only [positiveRun]
  split
  · simp only [List.length_append,List.length_cons,List.length_nil]
    unfold positiveCount
    omega
  · split
    · simp only [List.length_append,List.length_cons,List.length_nil]
      unfold positiveCount
      omega
    · rename_i after entries returned
      have out' := transport_length (G:=input.graph) rfl
        (show (fun i : Fin h => (zeroTarget target source lengths).value[i.val]) = Rounding.positiveTarget
          (fun i => source[i.val]) (fun i => target[i.val]) (fun i => lengths[i.val]) from
          funext (zeroTarget_get target source lengths))
        (StoredCore.run input buying physical opening budget (allowance lengths).value source
          (zeroTarget target source lengths).value (activeFlags lengths true).value ratio r seed ratio_ge).value
      rw [returned] at out'
      simp only [resultLength] at out' out
      have projected := projectPositiveEntries_count input source target lengths entries
      simp only [List.length_append,List.length_cons,List.length_nil]
      unfold positiveCount
      omega

def positiveInputBudget (L : ℕ) := phaseScalarBudget L+8

def positiveWords (n h L : ℕ) := StoredCore.coreWords n h (positiveInputBudget L)+n+h+phaseScalarBudget L+L+30

theorem positiveRun_words (buying physical opening : Vector ℚ n) (budget : ℚ)
    (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (ratio r : ℕ) (seed : Vector Bool n) (ratio_ge : 2 ≤ ratio) (L : ℕ) (constant : 8 ≤ L)
    (buying_width : ∀ v : Fin n, (Code.ofRat buying[v.val]).bits ≤ L)
    (physical_width : ∀ v : Fin n, (Code.ofRat physical[v.val]).bits ≤ L)
    (opening_width : ∀ v : Fin n, (Code.ofRat opening[v.val]).bits ≤ L)
    (budget_width : (Code.ofRat budget).bits ≤ L) (lengths_width : ∀ i : Fin h, (Code.ofRat lengths[i.val]).bits ≤ L)
    (ratio_width : ratio.size ≤ L) (r_width : r.size ≤ L) :
    WordsWithin (positiveWords n h L)
      (positiveRun input buying physical opening budget source target lengths ratio r seed ratio_ge).events := by
  let K := positiveWords n h L
  let S := positiveInputBudget L
  have LS : L ≤ S := by dsimp [S,positiveInputBudget,phaseScalarBudget];omega
  have one : 1 ≤ K := by dsimp [K,positiveWords];omega
  have nn : n.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp [K,positiveWords];omega)
  have hh : h.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp [K,positiveWords];omega)
  have active := (activeFlags_words lengths true L lengths_width).mono
    (show h+phaseScalarBudget L ≤ K by dsimp [K,positiveWords];omega)
  have empty := (activeEmpty_words (activeFlags lengths true).value).mono
    (show h+1 ≤ K by dsimp [K,positiveWords];omega)
  have allowances := (allowance_words lengths L lengths_width).mono
    (show h+phaseScalarBudget L ≤ K by dsimp [K,positiveWords];omega)
  have dummy := (zeroTarget_words target source lengths L lengths_width).mono
    (show n+h+phaseScalarBudget L ≤ K by dsimp [K,positiveWords];omega)
  have allowance_width (i : Fin h) : (Code.ofRat (allowance lengths).value[i.val]).bits ≤ S :=
    (allowance_bits lengths L lengths_width i).trans (by dsimp [S,positiveInputBudget];omega)
  have core := (StoredCore.run_words input buying physical opening budget (allowance lengths).value source
    (zeroTarget target source lengths).value (activeFlags lengths true).value ratio r seed ratio_ge S (by omega)
    (fun v => (buying_width v).trans LS) (fun v => (physical_width v).trans LS) (fun v => (opening_width v).trans LS)
    (budget_width.trans LS) allowance_width (ratio_width.trans LS) (r_width.trans LS)).mono
    (show StoredCore.coreWords n h S ≤ K by dsimp [K,positiveWords,S];omega)
  simp only [positiveRun]
  split
  · simp only [wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
    aesop
  · split
    · simp only [wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
      aesop
    · rename_i after entries returned
      have projected := (projectPositiveEntries_words input source target lengths entries L lengths_width).mono
        (show n+h+L+10 ≤ K by dsimp [K,positiveWords];omega)
      simp only [wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,and_true]
      aesop

end BuyAtBulk.Computation.Runtime.StoredRounding
