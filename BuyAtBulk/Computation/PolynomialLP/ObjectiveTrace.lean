import BuyAtBulk.Computation.PolynomialLP.BisectionTrace
import BuyAtBulk.Computation.PolynomialLP.ReconstructionComplete
import BuyAtBulk.Computation.PolynomialLP.BudgetTrace
import BuyAtBulk.Computation.PolynomialLP.CutTrace
import BuyAtBulk.Computation.PolynomialLP.ValueOptimization

/-! Exact objective recovery with explicit arithmetic schedules and constraint
allocation. The traced decision parameter is instantiated by the independently
verified feasibility implementation in the complete solver composition. -/
namespace BuyAtBulk.PolynomialLP.ObjectiveRuntime
open Computation Computation.Runtime Computation.Rational
variable {n m : ℕ}

def addNat (a b : ℕ) : Traced ℕ := emit .natAdd [a.size,b.size,(a+b).size] (a+b)

structure Schedule where
  bits : ℕ
  bracket : Bracket
  rounds : ℕ
  denominator : ℕ

def schedule (input : Stored (n:=n) (m:=m)) (K : ℕ) : Traced Schedule := do
  let L ← InputTrace.vectorBudget input.objective
  let fourN ← natMul 4 n
  let factor ← addNat fourN 1
  let factor ← natMul 2 factor
  let base ← addNat L K
  let base ← addNat base 5
  let product ← natMul factor base
  let B ← addNat product 2
  let exponent ← addNat L n
  let exponent ← addNat exponent 2
  let magnitude ← powerTwo exponent
  let upper ← ratCast magnitude
  let lower ← emit .ratNeg [(Code.ofRat upper).bits,(Code.ofRat (-upper)).bits] (-upper)
  let bracket ← emit .write [(Code.ofRat lower).bits,(Code.ofRat upper).bits] (Bracket.mk lower upper)
  let depth ← addNat B 1
  let twice ← natMul 2 depth
  let rounds ← addNat exponent twice
  let rounds ← addNat rounds 3
  let denominator ← powerTwo depth
  emit .write [B.size,rounds.size,denominator.size] ⟨B,bracket,rounds,denominator⟩

theorem schedule_value (input : Stored (n:=n) (m:=m)) (K : ℕ) :
    (schedule input K).value=
      ⟨valueBits input K,searchBracket n (objectiveBits input),
        searchRounds n (objectiveBits input) (valueBits input K),2^(valueBits input K+1)⟩ := by
  simp [schedule,Traced.bind_value,addNat,natMul,powerTwo_value,ratCast,
    valueBits,objectiveBits,searchBracket,searchMagnitude,searchRounds,Nat.cast_pow,Nat.cast_ofNat]

theorem schedule_count (input : Stored (n:=n) (m:=m)) (K : ℕ) :
    (schedule input K).events.length≤(InputTrace.vectorBudget input.objective).events.length+
      2*(objectiveBits input+n+2)+2*(valueBits input K+1)+24 := by
  have add_count (a b : ℕ) : (addNat a b).events.length=1 := rfl
  have mul_count (a b : ℕ) : (natMul a b).events.length=1 := rfl
  have cast_count (a : ℕ) : (ratCast a).events.length=1 := rfl
  simp only [schedule,Traced.bind_events,Traced.bind_value,emit_length,emit_value,List.length_append,
    add_count,mul_count,cast_count,InputTrace.vectorBudget_value,powerTwo_count,powerTwo_value,natMul,addNat,
    valueBits,objectiveBits,ratCast]
  omega

def belowTrace (oracle : {m : ℕ} → Stored (n:=n) (m:=m) → Traced Bool)
    (input : Stored (n:=n) (m:=m)) (threshold : ℚ) : Traced Bool := do
  let cut ← addCutTrace input input.objective threshold
  oracle cut

@[simp] theorem belowTrace_value
    (oracle : {m : ℕ} → Stored (n:=n) (m:=m) → Traced Bool)
    (input : Stored (n:=n) (m:=m)) (threshold : ℚ) :
    (belowTrace oracle input threshold).value=(oracle (input.addCut input.objective threshold)).value := by
  simp [belowTrace,Traced.bind_value]

def recover (oracle : {m : ℕ} → Stored (n:=n) (m:=m) → Traced Bool)
    (input : Stored (n:=n) (m:=m)) (K : ℕ) : Traced (Option ℚ) := do
  let parameters ← schedule input K
  let bracket ← bisectTrace (belowTrace oracle input) parameters.rounds parameters.bracket
  ReconstructionRuntime.reconstructComplete bracket.lower bracket.upper parameters.denominator

 theorem recover_value
    (oracle : {m : ℕ} → Stored (n:=n) (m:=m) → Traced Bool)
    (correct : ∀ {m : ℕ} (input : Stored (n:=n) (m:=m)), (oracle input).value=decideBoxed input)
    (input : Stored (n:=n) (m:=m)) (K : ℕ) :
    (recover oracle input K).value=recoverValue input K := by
  simp [recover,Traced.bind_value,schedule_value,correct,recoverValue,recoverObjective,below] <;> rfl

end BuyAtBulk.PolynomialLP.ObjectiveRuntime
