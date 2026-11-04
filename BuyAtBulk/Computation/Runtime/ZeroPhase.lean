import BuyAtBulk.Computation.Runtime.GraphTransport
import BuyAtBulk.Computation.Runtime.ZeroGraph
import BuyAtBulk.Computation.Runtime.ZeroProjectionRuntime
import BuyAtBulk.Computation.Runtime.ZeroRestriction

namespace BuyAtBulk.Computation.Runtime.StoredRounding
open BuyAtBulk.UpperBound
open Rational
variable {n h : ℕ} (input : ShortestPath.GraphEncoding n)

theorem free_zero_transport {G H : SimpleGraph (Fin n)} [leftDec : DecidableRel G.Adj] [rightDec : DecidableRel H.Adj]
    (graph_eq : G=H) {source target target' : Fin h → Fin n} (target_eq : target=target')
    (buying : Fin n → ℚ) (order : List (Fin h)) :
    transportSemantic graph_eq target_eq
      ((Rounding.freeRoutes G (Equiv.refl _) (fun _ => 0) source target (fun _ => 0)
        (Rounding.zeroState G (Equiv.refl _) buying) order).map fun entries =>
          (Rounding.zeroState G (Equiv.refl _) buying,entries)) =
      (Rounding.freeRoutes H (Equiv.refl _) (fun _ => 0) source target' (fun _ => 0)
        (Rounding.zeroState H (Equiv.refl _) buying) order).map fun entries =>
          (Rounding.zeroState H (Equiv.refl _) buying,entries) := by
  cases graph_eq
  cases target_eq
  cases Subsingleton.elim leftDec rightDec
  rfl

@[simp] theorem restrictedBudget_value (physical buying opening : Vector ℚ n) :
    (ArrayDot.run buying (restrictedOpening physical buying opening).value).value=
      Rounding.restrictedBudget (fun v : Fin n => buying[v.val]) (fun v : Fin n => physical[v.val]) (fun v : Fin n => opening[v.val]) := by
  simp only[ArrayDot.run_value,restrictedOpening_get,Rounding.restrictedBudget]

def zeroRaw (buying physical opening : Vector ℚ n) (source target : Vector (Fin n) h) (lengths : Vector ℚ h) :
    Traced (StoredResult (zeroGraph input.graph (fun v : Fin n => physical[v.val])) (fun i : Fin h => source[i.val])
      (Rounding.zeroTarget (fun i : Fin h => source[i.val]) (fun i : Fin h => target[i.val]) (fun i : Fin h => lengths[i.val]))) :=
  let graph := zeroInput input physical
  let zeros := constantVector n (0 : ℚ) 3
  let restricted := restrictedOpening physical buying opening
  let budget := ArrayDot.run buying restricted.value
  let dummy := zeroTarget source target lengths
  let ones := constantVector h (1 : ℚ) 4
  let active := activeFlags lengths false
  let order := StoredCore.requestOrder active.value ones.value
  let free := zeroTest budget.value
  let result : Traced (StoredResult graph.value.graph (fun i : Fin h => source[i.val]) (fun i : Fin h => dummy.value[i.val])) := if free.value then
      let state := zeroState graph.value buying
      let limits := constantVector h (0 : ℚ) 3
      let routes := freeRoutes graph.value zeros.value source dummy.value limits.value state.value order.value
      ⟨routes.value.map (fun entries => (state.value,entries)),
        state.events++limits.events++routes.events++[⟨.branch,[1]⟩,⟨.cons,[n.size,h.size]⟩]⟩
    else
      let depth := binaryDepth h
      let seed := constantVector n false 1
      let answer := StoredCore.run graph.value buying zeros.value restricted.value budget.value ones.value source dummy.value active.value 8 depth.value seed.value (by decide)
      ⟨answer.value,depth.events++seed.events++answer.events⟩
  ⟨transportResult (zeroInput_graph input physical) (funext (zeroTarget_get source target lengths)) result.value,
    graph.events++zeros.events++restricted.events++budget.events++dummy.events++ones.events++active.events++order.events++
      free.events++[⟨.branch,[1]⟩]++result.events⟩

theorem zeroRaw_value (buying physical opening : Vector ℚ n) (source target : Vector (Fin n) h) (lengths : Vector ℚ h) :
    decodeResult (zeroGraph input.graph (fun v : Fin n => physical[v.val])) (fun i : Fin h => source[i.val])
      (Rounding.zeroTarget (fun i : Fin h => source[i.val]) (fun i : Fin h => target[i.val]) (fun i : Fin h => lengths[i.val]))
      (zeroRaw input buying physical opening source target lengths).value =
    letI := Rounding.zeroGraphDecidableAdj input.graph (fun v : Fin n => physical[v.val])
    let graph := zeroGraph input.graph (fun v : Fin n => physical[v.val])
    let budget := Rounding.restrictedBudget (fun v : Fin n => buying[v.val]) (fun v : Fin n => physical[v.val]) (fun v : Fin n => opening[v.val])
    if budget=0 then
      (Rounding.freeRoutes graph (Equiv.refl _) (fun _ => 0) (fun i : Fin h => source[i.val])
        (Rounding.zeroTarget (fun i : Fin h => source[i.val]) (fun i : Fin h => target[i.val]) (fun i : Fin h => lengths[i.val])) (fun _ => 0)
        (Rounding.zeroState graph (Equiv.refl _) (fun v : Fin n => buying[v.val]))
        (CoreRun.requestOrder (Rounding.zeroActive (fun i : Fin h => lengths[i.val])) (fun _ => 1))).map
          fun entries => (Rounding.zeroState graph (Equiv.refl _) (fun v : Fin n => buying[v.val]),entries)
    else Core.run graph (Equiv.refl _) (fun v : Fin n => buying[v.val]) (fun _ => 0)
      (Rounding.restrictedOpening (fun v : Fin n => buying[v.val]) (fun v : Fin n => physical[v.val]) (fun v : Fin n => opening[v.val])) budget
      (fun _ => 1) (fun i : Fin h => source[i.val])
      (Rounding.zeroTarget (fun i : Fin h => source[i.val]) (fun i : Fin h => target[i.val]) (fun i : Fin h => lengths[i.val]))
      (Rounding.zeroActive (fun i : Fin h => lengths[i.val])) 8 (UpperBound.binaryDepth h) ∅ := by
  letI := Rounding.zeroGraphDecidableAdj input.graph (fun v : Fin n => physical[v.val])
  simp only[zeroRaw,zeroTest_value,restrictedBudget_value,decide_eq_true_eq]
  split_ifs with free
  · rw [decode_transport]
    simp only[decodeResult,Option.map_map,freeRoutes_value,zeroState_value,
      StoredCore.requestOrder_value,activeFlags_zeroSet,constantVector_get,Function.comp_def,zeroState_value]
    exact free_zero_transport (zeroInput_graph input physical) (funext (zeroTarget_get source target lengths)) _ _
  · rw [decode_transport]
    change transportSemantic _ _ (StoredBatch.decodeOption _ _ _ _) = _
    rw [StoredCore.run_value,core_transport]
    simp only[constantVector_get,restrictedOpening_get,restrictedBudget_value,activeFlags_zeroSet,binaryDepth_value,constantFalse_set]

def zeroRun (buying physical opening : Vector ℚ n) (_budget : ℚ) (source target : Vector (Fin n) h) (lengths : Vector ℚ h) :
    Traced (StoredResult (zeroGraph input.graph (fun v : Fin n => physical[v.val])) (fun i : Fin h => source[i.val])
      (Rounding.zeroTarget (fun i : Fin h => source[i.val]) (fun i : Fin h => target[i.val]) (fun i : Fin h => lengths[i.val]))) :=
  let active := activeFlags lengths false
  let empty := activeEmpty active.value
  let header := active.events++empty.events++[⟨Operation.branch,[1]⟩]
  if empty.value then
    let flags := constantVector n false 1
    ⟨some (⟨flags.value,[],[]⟩,[]),header++flags.events++[⟨.cons,[n.size]⟩]⟩
  else
    let result := zeroRaw input buying physical opening source target lengths
    match result.value with
    | none => ⟨none,header++result.events++[⟨.branch,[1]⟩]⟩
    | some (state,entries) =>
      let masked := maskBought physical state.bought
      ⟨some ({state with bought := masked.value},entries),
        header++result.events++[⟨.branch,[1]⟩]++masked.events++[⟨.cons,[n.size]⟩]⟩

theorem zeroRun_value (buying physical opening : Vector ℚ n) (budget : ℚ) (source target : Vector (Fin n) h) (lengths : Vector ℚ h) :
    decodeResult (zeroGraph input.graph (fun v : Fin n => physical[v.val])) (fun i : Fin h => source[i.val])
      (Rounding.zeroTarget (fun i : Fin h => source[i.val]) (fun i : Fin h => target[i.val]) (fun i : Fin h => lengths[i.val]))
      (zeroRun input buying physical opening budget source target lengths).value=
      Rounding.zeroRun input.graph (Equiv.refl _) (fun v : Fin n => buying[v.val]) (fun v : Fin n => physical[v.val]) (fun v : Fin n => opening[v.val]) budget
        (fun i : Fin h => source[i.val]) (fun i : Fin h => target[i.val]) (fun i : Fin h => lengths[i.val]) := by
  letI := Rounding.zeroGraphDecidableAdj input.graph (fun v : Fin n => physical[v.val])
  simp only[zeroRun,Rounding.zeroRun,activeEmpty_value,activeFlags_zeroSet,decide_eq_true_eq]
  by_cases empty : Rounding.zeroActive (fun i : Fin h => lengths[i.val])=∅
  · simp only[empty,ite_true,decodeResult,Option.map_some,StoredState.decode,constantFalse_set]
  · simp only[empty,ite_false]
    rw [←zeroRaw_value]
    cases result : (zeroRaw input buying physical opening source target lengths).value with
    | none => rfl
    | some pair =>
      rcases pair with ⟨state,entries⟩
      simp only[decodeResult,Option.map_some,StoredState.decode,Rounding.restrictZeroState,maskBought_set]

def zeroRawCount (n h : ℕ) :=
  (n*(8*n+3)+2)+(3*n+1)+(9*n+1)+10*n+(6*h+1)+(3*h+1)+(5*h+1)+StoredCore.requestOrderCount h+2+
  (4*n+2)+(3*h+1)+h*(AttachmentQueries.routeBudget n+12*n+8)+3+
  (10*h+4)+(3*n+1)+StoredCore.coreCount n h

theorem zeroRaw_count (buying physical opening : Vector ℚ n) (source target : Vector (Fin n) h) (lengths : Vector ℚ h) :
    (zeroRaw input buying physical opening source target lengths).events.length ≤ zeroRawCount n h := by
  have graph := zeroInput_count input physical
  have zeros := constantVector_count n (0 : ℚ) 3
  have restricted := restrictedOpening_count physical buying opening
  have dot := ArrayDot.run_count buying (restrictedOpening physical buying opening).value
  have dummy := zeroTarget_count source target lengths
  have ones := constantVector_count h (1 : ℚ) 4
  have active := activeFlags_count lengths false
  have order := StoredCore.requestOrder_count (activeFlags lengths false).value (constantVector h (1 : ℚ) 4).value
  have orderLength := StoredCore.requestOrder_length (activeFlags lengths false).value (constantVector h (1 : ℚ) 4).value
  have depth := binaryDepth_count h
  have seed := constantVector_count n false 1
  have answer := StoredCore.run_count (zeroInput input physical).value buying (constantVector n (0 : ℚ) 3).value
    (restrictedOpening physical buying opening).value (ArrayDot.run buying (restrictedOpening physical buying opening).value).value
    (constantVector h (1 : ℚ) 4).value source (zeroTarget source target lengths).value
    (activeFlags lengths false).value 8 (binaryDepth h).value (constantVector n false 1).value (by decide)
  have state := zeroState_count (zeroInput input physical).value buying
  have limits := constantVector_count h (0 : ℚ) 3
  have routes := freeRoutes_count (zeroInput input physical).value (constantVector n (0 : ℚ) 3).value
    source (zeroTarget source target lengths).value (constantVector h (0 : ℚ) 3).value
    (zeroState (zeroInput input physical).value buying).value
    (StoredCore.requestOrder (activeFlags lengths false).value (constantVector h (1 : ℚ) 4).value).value
  have routeBound := Nat.mul_le_mul_right (AttachmentQueries.routeBudget n+12*n+8) orderLength
  simp only[zeroRaw]
  split <;>simp only[List.length_append,List.length_cons,List.length_nil,zeroTest,emit_length]
  all_goals unfold zeroRawCount;omega

def zeroCount (n h : ℕ) := (5*h+1)+(7*h+2)+(3*n+1)+zeroRawCount n h+(6*n+1)+4

theorem zeroRun_count (buying physical opening : Vector ℚ n) (budget : ℚ) (source target : Vector (Fin n) h) (lengths : Vector ℚ h) :
    (zeroRun input buying physical opening budget source target lengths).events.length ≤ zeroCount n h := by
  have active := activeFlags_count lengths false
  have empty := activeEmpty_count (activeFlags lengths false).value
  have flags := constantVector_count n false 1
  have raw := zeroRaw_count input buying physical opening source target lengths
  simp only[zeroRun]
  split
  · simp only[List.length_append,List.length_cons,List.length_nil]
    unfold zeroCount;omega
  · split
    · simp only[List.length_append,List.length_cons,List.length_nil]
      unfold zeroCount;omega
    · rename_i state entries result
      have mask := maskBought_count physical state.bought
      simp only[List.length_append,List.length_cons,List.length_nil]
      unfold zeroCount;omega

def zeroInputBudget (n h L : ℕ) := 2*(4*n+1)*(L+1)+L+2*h+20

def zeroWords (n h L : ℕ) := StoredCore.coreWords n h (zeroInputBudget n h L)+ArrayDot.wordBudget n (L+1)+
  StoredAttachment.wordBudget n 0 L+binaryDepthWords h+zeroInputBudget n h L+4*n+4*h+phaseScalarBudget L+L+100

theorem zeroRaw_words (buying physical opening : Vector ℚ n) (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (L : ℕ) (constant : 8 ≤ L)
    (buying_width : ∀ v : Fin n, (Code.ofRat buying[v.val]).bits ≤ L)
    (physical_width : ∀ v : Fin n, (Code.ofRat physical[v.val]).bits ≤ L)
    (opening_width : ∀ v : Fin n, (Code.ofRat opening[v.val]).bits ≤ L)
    (lengths_width : ∀ i : Fin h, (Code.ofRat lengths[i.val]).bits ≤ L) :
    WordsWithin (zeroWords n h L) (zeroRaw input buying physical opening source target lengths).events := by
  let K := zeroWords n h L
  let S := zeroInputBudget n h L
  have LS : L ≤ S := by dsimp[S,zeroInputBudget];omega
  have one : 1 ≤ K := by dsimp[K,zeroWords];omega
  have ni : n ≤ K := by dsimp[K,zeroWords];omega
  have hi : h ≤ K := by dsimp[K,zeroWords];omega
  have nn := (Nat.size_le.mpr Nat.lt_two_pow_self : n.size≤n).trans ni
  have hh := (Nat.size_le.mpr Nat.lt_two_pow_self : h.size≤h).trans hi
  have graph := (zeroInput_words input physical L physical_width).mono (show n+L+5 ≤ K by dsimp[K,zeroWords];omega)
  have zeros := (constantVector_words n (0 : ℚ) 3).mono (show n+3+1 ≤ K by dsimp[K,zeroWords];omega)
  have restricted := (restrictedOpening_words physical buying opening L (by omega) physical_width buying_width opening_width).mono
    (show n+L+5≤K by dsimp[K,zeroWords];omega)
  have restrictedBits := restrictedOpening_bits physical buying opening L (by omega) opening_width
  have dot := (ArrayDot.run_words buying (restrictedOpening physical buying opening).value (L+1) (by omega)
    (fun v => by have := buying_width v;omega) (fun v => by have := restrictedBits v;omega)).mono
      (show ArrayDot.wordBudget n (L+1)≤K by dsimp[K,zeroWords];omega)
  have dotBits := ArrayDot.run_bits buying (restrictedOpening physical buying opening).value (L+1) (by omega)
    (fun v => by have := buying_width v;omega) (fun v => by have := restrictedBits v;omega)
  have budgetS : (Code.ofRat (ArrayDot.run buying (restrictedOpening physical buying opening).value).value).bits≤S :=
    dotBits.trans (by dsimp[S,zeroInputBudget];omega)
  have budgetK : (Code.ofRat (ArrayDot.run buying (restrictedOpening physical buying opening).value).value).bits≤K :=
    dotBits.trans (by
      dsimp[K,zeroWords,zeroInputBudget]
      omega)
  have dummy := (zeroTarget_words source target lengths L lengths_width).mono (show n+h+phaseScalarBudget L ≤ K by dsimp[K,zeroWords];omega)
  have ones := (constantVector_words h (1 : ℚ) 4).mono (show h+4+1 ≤ K by dsimp[K,zeroWords];omega)
  have active := (activeFlags_words lengths false L lengths_width).mono (show h+phaseScalarBudget L ≤ K by dsimp[K,zeroWords];omega)
  have one_width : ∀ i : Fin h, (Code.ofRat (constantVector h (1 : ℚ) 4).value[i.val]).bits ≤ L := by
    intro i
    simp only[constantVector_get]
    rw [show (Code.ofRat 1).bits=4 by decide];omega
  have zero_width : ∀ v : Fin n, (Code.ofRat (constantVector n (0 : ℚ) 3).value[v.val]).bits ≤ L := by
    intro v
    simp only[constantVector_get]
    rw [show (Code.ofRat 0).bits=3 by decide];omega
  have limit_width : ∀ i : Fin h, (Code.ofRat (constantVector h (0 : ℚ) 3).value[i.val]).bits ≤ L := by
    intro i
    simp only[constantVector_get]
    rw [show (Code.ofRat 0).bits=3 by decide];omega
  have order := (StoredCore.requestOrder_words (activeFlags lengths false).value (constantVector h (1 : ℚ) 4).value L one_width).mono
    (show 2*h+L+5≤K by dsimp[K,zeroWords];omega)
  have depth := (binaryDepth_words h).mono (show binaryDepthWords h ≤ K by dsimp[K,zeroWords];omega)
  have seed := (constantVector_words n false 1).mono (show n+1+1 ≤ K by dsimp[K,zeroWords];omega)
  have depth_width : (binaryDepth h).value.size ≤ S := by
    rw[binaryDepth_value]
    have bounded : UpperBound.binaryDepth h ≤ 2*h := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[S,zeroInputBudget];omega)
  have answer := (StoredCore.run_words (zeroInput input physical).value buying (constantVector n (0 : ℚ) 3).value
    (restrictedOpening physical buying opening).value (ArrayDot.run buying (restrictedOpening physical buying opening).value).value
    (constantVector h (1 : ℚ) 4).value source (zeroTarget source target lengths).value
    (activeFlags lengths false).value 8 (binaryDepth h).value (constantVector n false 1).value (by decide)
    S (by omega) (fun v => (buying_width v).trans LS) (fun v => (zero_width v).trans LS)
    (fun v => (restrictedBits v).trans LS) budgetS (fun i => (one_width i).trans LS)
    (by rw[show (8 : ℕ).size=4 by decide];omega) depth_width).mono
    (show StoredCore.coreWords n h S ≤ K by dsimp[K,zeroWords,S];omega)
  have state := (zeroState_words (zeroInput input physical).value buying L buying_width).mono
    (show n+L+5≤K by dsimp[K,zeroWords];omega)
  have limits := (constantVector_words h (0 : ℚ) 3).mono (show h+3+1≤K by dsimp[K,zeroWords];omega)
  have routes := (freeRoutes_words (zeroInput input physical).value (constantVector n (0 : ℚ) 3).value
    source (zeroTarget source target lengths).value (constantVector h (0 : ℚ) 3).value
    (zeroState (zeroInput input physical).value buying).value
    (StoredCore.requestOrder (activeFlags lengths false).value (constantVector h (1 : ℚ) 4).value).value
    L constant zero_width limit_width).mono
    (show StoredAttachment.wordBudget n 0 L+n+h+10≤K by dsimp[K,zeroWords];omega)
  have three : 3≤K := by dsimp[K,zeroWords];omega
  simp only[zeroRaw]
  split <;>simp only[wordsWithin_append,zeroTest,emit,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
    or_false,forall_eq_or_imp,forall_eq,and_true]
  all_goals aesop

theorem zeroRun_words (buying physical opening : Vector ℚ n) (budget : ℚ) (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
    (L : ℕ) (constant : 8 ≤ L)
    (buying_width : ∀ v : Fin n, (Code.ofRat buying[v.val]).bits ≤ L)
    (physical_width : ∀ v : Fin n, (Code.ofRat physical[v.val]).bits ≤ L)
    (opening_width : ∀ v : Fin n, (Code.ofRat opening[v.val]).bits ≤ L)
    (_budget_width : (Code.ofRat budget).bits ≤ L) (lengths_width : ∀ i : Fin h, (Code.ofRat lengths[i.val]).bits ≤ L) :
    WordsWithin (zeroWords n h L) (zeroRun input buying physical opening budget source target lengths).events := by
  let K := zeroWords n h L
  have one : 1≤K := by dsimp[K,zeroWords];omega
  have nn : n.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp[K,zeroWords];omega)
  have active := (activeFlags_words lengths false L lengths_width).mono (show h+phaseScalarBudget L≤K by dsimp[K,zeroWords];omega)
  have empty := (activeEmpty_words (activeFlags lengths false).value).mono (show h+1≤K by dsimp[K,zeroWords];omega)
  have flags := (constantVector_words n false 1).mono (show n+1+1≤K by dsimp[K,zeroWords];omega)
  have raw := zeroRaw_words input buying physical opening source target lengths L constant buying_width physical_width opening_width lengths_width
  simp only[zeroRun]
  split
  · simp only[wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_singleton,forall_eq,and_true]
    exact ⟨⟨⟨⟨active,empty⟩,one⟩,flags⟩,nn⟩
  · split
    · simp only[wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_singleton,forall_eq,and_true]
      exact ⟨⟨⟨⟨active,empty⟩,one⟩,raw⟩,one⟩
    · rename_i state entries result
      have mask := (maskBought_words physical state.bought L physical_width).mono (show n+L+5≤K by dsimp[K,zeroWords];omega)
      simp only[wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_singleton,forall_eq,and_true]
      exact ⟨⟨⟨⟨⟨⟨active,empty⟩,one⟩,raw⟩,one⟩,mask⟩,nn⟩

end BuyAtBulk.Computation.Runtime.StoredRounding
