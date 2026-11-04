import BuyAtBulk.Computation.PolynomialLP.InputTrace
import BuyAtBulk.Computation.PolynomialLP.Normalization
import BuyAtBulk.Computation.Runtime.Logarithm

/-! Explicit normalization precision and input-bit schedules. No logarithm,
input-length or exponentiation oracle is evaluated by these data routines. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace BuyAtBulk.PolynomialLP.Trace
open BuyAtBulk.Computation BuyAtBulk.Computation.Runtime
open Rational

def addNat (a b : ℕ) : Traced ℕ := emit .natAdd [a.size, b.size, (a + b).size] (a + b)
def multiplyNat (a b : ℕ) : Traced ℕ := emit .natMul [a.size, b.size, (a * b).size] (a * b)
@[simp] theorem addNat_value (a b : ℕ) : (addNat a b).value = a + b := rfl
@[simp] theorem multiplyNat_value (a b : ℕ) : (multiplyNat a b).value = a * b := rfl
@[simp] theorem addNat_count (a b : ℕ) : (addNat a b).events.length = 1 := rfl
@[simp] theorem multiplyNat_count (a b : ℕ) : (multiplyNat a b).events.length = 1 := rfl

def normalizationPrecision (n : ℕ) : Traced ℕ := do
  let next ← addNat n 1
  let first ← multiplyNat 256 n
  let target ← multiplyNat first next
  ceilingLog 2 target target

theorem normalizationPrecision_value (n : ℕ) :
    (normalizationPrecision n).value = PolynomialLP.normalizationPrecision n := by
  simp only [normalizationPrecision, Traced.bind_value, addNat_value, multiplyNat_value]
  apply ceilingLog_value _ _ _ (by decide)
  exact Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le

theorem normalizationPrecision_count (n : ℕ) :
    (normalizationPrecision n).events.length ≤ 5 * (256 * n * (n + 1)) + 6 := by
  have count := logarithmLoop_count 2 (256 * n * (n + 1)) (256 * n * (n + 1)) 0 1
  simp only [normalizationPrecision, Traced.bind_events, Traced.bind_value, List.length_append,
    addNat_count, multiplyNat_count, addNat_value, multiplyNat_value, ceilingLog]
  omega

def rootFuel (q : ℚ) (n : ℕ) : Traced ℕ := do
  let bits ← InputTrace.codeBits q
  let precision ← normalizationPrecision n
  let next ← addNat bits 1
  let triple ← multiplyNat 3 next
  let sum ← addNat triple precision
  addNat sum 3

theorem rootFuel_value (q : ℚ) (n : ℕ) :
    (rootFuel q n).value = 3 * ((Code.ofRat q).bits + 1) + PolynomialLP.normalizationPrecision n + 3 := by
  simp only [rootFuel, Traced.bind_value, InputTrace.codeBits_value, normalizationPrecision_value,
    addNat_value, multiplyNat_value]

theorem rootFuel_count (q : ℚ) (n : ℕ) :
    (rootFuel q n).events.length ≤ 6 * (Code.ofRat q).bits + 5 * (256 * n * (n + 1)) + 20 := by
  have bits := InputTrace.codeBits_count q
  have precision := normalizationPrecision_count n
  simp only [rootFuel, Traced.bind_events, Traced.bind_value, List.length_append,
    addNat_count, multiplyNat_count]
  omega

def normalizationRoot (q : ℚ) (n : ℕ) : Traced ℚ :=
  let fuel := rootFuel q n
  let bracket := sqrtBracket q fuel.value
  ⟨bracket.value.2, fuel.events ++ bracket.events ++ [⟨.write, [(Code.ofRat bracket.value.2).bits]⟩]⟩

theorem normalizationRoot_value (q : ℚ) (n : ℕ) :
    (normalizationRoot q n).value = PolynomialLP.normalizationRoot q n := by
  simp only [normalizationRoot, rootFuel_value, PolynomialLP.normalizationRoot, relativeSqrt]

theorem normalizationRoot_count (q : ℚ) (n : ℕ) :
    (normalizationRoot q n).events.length ≤ 40 * ((Code.ofRat q).bits + 256 * n * (n + 1) + 3) := by
  have fuel := rootFuel_count q n
  have precision : PolynomialLP.normalizationPrecision n ≤ 256 * n * (n + 1) :=
    Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have bracket (F : ℕ) : (sqrtBracket q F).events.length = 9 * F + 2 := by
    simp only [sqrtBracket, Traced.bind_events, Traced.bind_value, List.length_append,
      ratAdd_length, sqrtBisect_count]
    omega
  simp only [normalizationRoot, List.length_append, List.length_cons, List.length_nil, bracket, rootFuel_value]
  omega

end BuyAtBulk.PolynomialLP.Trace
