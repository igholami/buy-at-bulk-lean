import BuyAtBulk.Computation.Runtime.CoreExecution
import BuyAtBulk.Computation.Rounding.Algorithm

namespace BuyAtBulk.Computation.Runtime.StoredRounding
open BuyAtBulk.UpperBound
open Rational
variable {n h : ℕ}

def zeroTest (q : ℚ) : Traced Bool := emit .ratCompare [(Code.ofRat q).bits,3] (decide (q=0))
@[simp] theorem zeroTest_value (q : ℚ) : (zeroTest q).value=decide (q=0) := rfl


def raisedCell (buying opening : Vector ℚ n) (v : Fin n) : Traced ℚ := do
  let buy ← readRat buying v
  let zero ← zeroTest buy
  let zero ← branch zero
  if zero then emit .write [(Code.ofRat 1).bits] 1 else readRat opening v

def raisedOpening (buying opening : Vector ℚ n) : Traced (Vector ℚ n) :=
  Weights.materialize (raisedCell buying opening) (fun q => (Code.ofRat q).bits)

@[simp] theorem raisedOpening_get (buying opening : Vector ℚ n) (v : Fin n) :
    (raisedOpening buying opening).value[v.val]=Rounding.raisedOpening (fun v => buying[v.val]) (fun v => opening[v.val]) v := by
  simp only[raisedOpening,Weights.materialize_get,raisedCell,Traced.bind_value,readRat,emit_value,zeroTest_value,branch]
  unfold Rounding.raisedOpening
  split_ifs <;>simp_all


def targetCell (source target : Vector (Fin n) h) (lengths : Vector ℚ h) (i : Fin h) : Traced (Fin n) := do
  let length ← readRat lengths i
  let zero ← zeroTest length
  let zero ← branch zero
  let result := if zero then target[i.val] else source[i.val]
  emit .read [i.val.size,result.val.size] result

def zeroTarget (source target : Vector (Fin n) h) (lengths : Vector ℚ h) : Traced (Vector (Fin n) h) :=
  Weights.materialize (targetCell source target lengths) (fun v => v.val.size)

@[simp] theorem zeroTarget_get (source target : Vector (Fin n) h) (lengths : Vector ℚ h) (i : Fin h) :
    (zeroTarget source target lengths).value[i.val]=Rounding.zeroTarget (fun i => source[i.val]) (fun i => target[i.val]) (fun i => lengths[i.val]) i := by
  simp only[zeroTarget,Weights.materialize_get,targetCell,Traced.bind_value,readRat,emit_value,zeroTest_value,branch]
  unfold Rounding.zeroTarget
  split_ifs <;>simp_all


def activeCell (lengths : Vector ℚ h) (positive : Bool) (i : Fin h) : Traced Bool := do
  let length ← readRat lengths i
  let zero ← zeroTest length
  emit .branch [1,1] (if positive then !zero else zero)

def activeFlags (lengths : Vector ℚ h) (positive : Bool) : Traced (Vector Bool h) :=
  Weights.materialize (activeCell lengths positive) (fun _ => 1)

@[simp] theorem activeFlags_get (lengths : Vector ℚ h) (positive : Bool) (i : Fin h) :
    (activeFlags lengths positive).value[i.val]=if positive then decide (lengths[i.val]≠0) else decide (lengths[i.val]=0) := by
  cases positive <;>by_cases zero : lengths[i.val]=0 <;>simp[activeFlags,Weights.materialize,activeCell,readRat,zeroTest,zero]


def allowanceCell (lengths : Vector ℚ h) (i : Fin h) : Traced ℚ := do
  let length ← readRat lengths i
  let zero ← zeroTest length
  let zero ← branch zero
  if zero then emit .write [(Code.ofRat 1).bits] 1 else ratMul 64 length

def allowance (lengths : Vector ℚ h) : Traced (Vector ℚ h) :=
  Weights.materialize (allowanceCell lengths) (fun q => (Code.ofRat q).bits)

@[simp] theorem allowance_get (lengths : Vector ℚ h) (i : Fin h) :
    (allowance lengths).value[i.val]=Rounding.allowance (fun i => lengths[i.val]) i := by
  simp only[allowance,Weights.materialize_get,allowanceCell,Traced.bind_value,readRat,emit_value,zeroTest_value,branch,ratMul_value]
  unfold Rounding.allowance
  split_ifs <;>simp_all


def constantVector {α : Type} (m : ℕ) (a : α) (width : ℕ) : Traced (Vector α m) :=
  Weights.materialize (fun _ : Fin m => emit .write [width] a) (fun _ => width)

@[simp] theorem constantVector_get {α : Type} (m : ℕ) (a : α) (width : ℕ) (i : Fin m) :
    (constantVector m a width).value[i.val]=a := by simp[constantVector,Weights.materialize]


def binaryDepth (h : ℕ) : Traced ℕ := do
  let target ← emit .natMul [2,h.size,(2*h).size] (2*h)
  ceilingLog 2 target target

@[simp] theorem binaryDepth_value (h : ℕ) : (binaryDepth h).value=UpperBound.binaryDepth h := by
  have bounded : Nat.clog 2 (2*h) ≤ 2*h := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
  simpa only[binaryDepth,Traced.bind_value,emit_value,UpperBound.binaryDepth] using ceilingLog_value 2 (2*h) (2*h) (by decide) bounded

theorem raisedOpening_count (buying opening : Vector ℚ n) : (raisedOpening buying opening).events.length ≤ 6*n+1 := by
  have per (v : Fin n) : (raisedCell buying opening v).events.length ≤ 4 := by
    simp only[raisedCell,Traced.bind_events,Traced.bind_value,readRat,emit_value,List.length_append,emit_length,zeroTest,branch]
    split_ifs <;>simp_all[emit]
  simpa only[raisedOpening,Nat.reduceAdd,Nat.mul_comm] using Weights.materialize_count (raisedCell buying opening) (fun q => (Code.ofRat q).bits) 4 per

theorem zeroTarget_count (source target : Vector (Fin n) h) (lengths : Vector ℚ h) :
    (zeroTarget source target lengths).events.length ≤ 6*h+1 := by
  have per (i : Fin h) : (targetCell source target lengths i).events.length ≤ 4 := by rfl
  simpa only[zeroTarget,Nat.reduceAdd,Nat.mul_comm] using Weights.materialize_count (targetCell source target lengths) (fun v => v.val.size) 4 per

theorem activeFlags_count (lengths : Vector ℚ h) (positive : Bool) : (activeFlags lengths positive).events.length ≤ 5*h+1 := by
  have per (i : Fin h) : (activeCell lengths positive i).events.length ≤ 3 := by rfl
  simpa only[activeFlags,Nat.reduceAdd,Nat.mul_comm] using Weights.materialize_count (activeCell lengths positive) (fun _ => 1) 3 per

theorem allowance_count (lengths : Vector ℚ h) : (allowance lengths).events.length ≤ 7*h+1 := by
  have per (i : Fin h) : (allowanceCell lengths i).events.length ≤ 5 := by
    simp only[allowanceCell,Traced.bind_events,Traced.bind_value,readRat,emit_value,List.length_append,emit_length,zeroTest,branch]
    split_ifs <;>simp_all[emit,ratMul_length]
  simpa only[allowance,Nat.reduceAdd,Nat.mul_comm] using Weights.materialize_count (allowanceCell lengths) (fun q => (Code.ofRat q).bits) 5 per

theorem constantVector_count {α : Type} (m : ℕ) (a : α) (width : ℕ) :
    (constantVector m a width).events.length ≤ 3*m+1 := by
  simpa only[constantVector,Nat.reduceAdd,Nat.mul_comm] using Weights.materialize_count
    (fun _ : Fin m => emit .write [width] a) (fun _ => width) 1 (by intro;rfl)

theorem binaryDepth_count (h : ℕ) : (binaryDepth h).events.length ≤ 10*h+4 := by
  have count := logarithmLoop_count 2 (2*h) (2*h) 0 1
  simp only[binaryDepth,Traced.bind_events,Traced.bind_value,emit_value,emit_length,List.length_append,ceilingLog]
  omega

end BuyAtBulk.Computation.Runtime.StoredRounding
