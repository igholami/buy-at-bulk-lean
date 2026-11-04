import BuyAtBulk.Computation.Runtime.Numerical
import BuyAtBulk.Computation.Parameters

namespace BuyAtBulk.Computation.Runtime.OptimizedParameters
open BuyAtBulk.UpperBound

/-- Increasing bounded search, evaluating every tested integer power by its
actual multiplication loop. -/
def qSearch (target : ℕ) : ℕ → ℕ → Traced ℕ
  | 0,current => emit .write [current.size] current
  | fuel+1,current =>
    let powered := power current current
    let test := emit .natCompare [target.size,powered.value.size] (decide (target≤powered.value))
    let control := powered.events++test.events++[⟨Operation.branch,[1]⟩]
    if test.value then ⟨current,control++[⟨.write,[current.size]⟩]⟩ else
      let increment := emit .natAdd [current.size,1,(current+1).size] (current+1)
      let next := qSearch target fuel increment.value
      ⟨next.value,control++increment.events++next.events⟩


theorem qSearch_value (h fuel current : ℕ) (lower : 2≤current) (upper : current≤Optimization.q h)
    (enough : Optimization.q h<current+fuel) : (qSearch (2*h) fuel current).value=Optimization.q h := by
  induction fuel generalizing current with
  | zero => omega
  | succ k ih =>
    simp only[qSearch,power_value,emit_value]
    by_cases qualifying : 2*h≤current^current
    · simp only[qualifying,decide_true,ite_true]
      have least := Optimization.q_le lower qualifying
      omega
    · simp only[qualifying,decide_false,Bool.false_eq_true,ite_false,emit_value]
      have strict : current<Optimization.q h := by
        have spec := (Optimization.q_spec h).2
        by_contra wrong
        have same : current=Optimization.q h := by omega
        exact qualifying (same.symm ▸ spec)
      exact ih (current+1) (by omega) (by omega) (by omega)


def q (h : ℕ) : Traced ℕ := do
  let target ← emit .natMul [2,h.size,(2*h).size] (2*h)
  let fuel ← emit .natAdd [target.size,1,(target+1).size] (target+1)
  qSearch target fuel 2

@[simp] theorem q_value (h : ℕ) : (q h).value=Optimization.q h := by
  have bound : Optimization.q h≤2*h+2 := by rw[←Parameters.q_eq];exact Parameters.q_bound h
  simpa only[q,Traced.bind_value,emit_value] using qSearch_value h (2*h+1) 2 (by omega) (Optimization.q_spec h).1 (by omega)


def squareSearch (target : ℕ) : ℕ → ℕ → Traced ℕ
  | 0,current => emit .write [current.size] current
  | fuel+1,current =>
    let square := emit .natMul [current.size,current.size,(current*current).size] (current*current)
    let test := emit .natCompare [target.size,square.value.size] (decide (target≤square.value))
    let control := square.events++test.events++[⟨Operation.branch,[1]⟩]
    if test.value then ⟨current,control++[⟨.write,[current.size]⟩]⟩ else
      let increment := emit .natAdd [current.size,1,(current+1).size] (current+1)
      let next := squareSearch target fuel increment.value
      ⟨next.value,control++increment.events++next.events⟩


theorem ceilSqrt_le_self (n : ℕ) : Parameters.ceilSqrt n≤n := by
  apply Finset.min'_le
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by simpa only[pow_two] using Nat.le_mul_self n⟩


theorem squareSearch_value (target fuel current : ℕ) (upper : current≤Parameters.ceilSqrt target)
    (enough : Parameters.ceilSqrt target<current+fuel) :
    (squareSearch target fuel current).value=Parameters.ceilSqrt target := by
  induction fuel generalizing current with
  | zero => omega
  | succ k ih =>
    simp only[squareSearch,emit_value]
    by_cases qualifying : target≤current*current
    · simp only[qualifying,decide_true,ite_true]
      have bound := ceilSqrt_le_self target
      have least : Parameters.ceilSqrt target≤current := by
        apply Finset.min'_le
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by simpa only[pow_two] using qualifying⟩
      omega
    · simp only[qualifying,decide_false,Bool.false_eq_true,ite_false,emit_value]
      have strict : current<Parameters.ceilSqrt target := by
        have spec := Parameters.ceilSqrt_spec target
        by_contra wrong
        have same : current=Parameters.ceilSqrt target := by omega
        exact qualifying (by simpa only[same,pow_two] using spec)
      exact ih (current+1) (by omega) (by omega)


def ceilSqrt (target : ℕ) : Traced ℕ := do
  let fuel ← emit .natAdd [target.size,1,(target+1).size] (target+1)
  squareSearch target fuel 0

@[simp] theorem ceilSqrt_value (target : ℕ) : (ceilSqrt target).value=Parameters.ceilSqrt target := by
  have bound := ceilSqrt_le_self target
  simpa only[ceilSqrt,Traced.bind_value,emit_value] using squareSearch_value target (target+1) 0 (by omega) (by omega)


structure Values where
  q : ℕ
  ratio : ℕ
  girth : ℕ
  deriving Repr

def compute (h : ℕ) : Traced Values := do
  let parameter ← q h
  let root ← ceilSqrt parameter
  let test ← emit .natCompare [4,root.size] (decide (8≤root))
  let ratio ← emit .branch [1] (if test then root else 8)
  let girth ← emit .natMul [2,parameter.size,(2*parameter).size] (2*parameter)
  emit .cons [parameter.size,ratio.size,girth.size] ⟨parameter,ratio,girth⟩

@[simp] theorem compute_value (h : ℕ) :
    (compute h).value=⟨Optimization.q h,Optimization.scaleRatio h,Optimization.r h⟩ := by
  simp only[compute,Traced.bind_value,emit_value,q_value,ceilSqrt_value,Parameters.ceilSqrt_eq,
    Optimization.scaleRatio,Optimization.r,max_def]
  split_ifs <;>simp_all

end BuyAtBulk.Computation.Runtime.OptimizedParameters
