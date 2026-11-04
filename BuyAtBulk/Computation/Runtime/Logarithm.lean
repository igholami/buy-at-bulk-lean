import BuyAtBulk.Computation.Runtime.Numerical
import BuyAtBulk.Computation.Runtime.Schedule

/-! Explicit ceiling-logarithm scan. Fuel is supplied with a proved polynomial
bound for each use; no logarithm or exponentiation oracle is called. -/
namespace BuyAtBulk.Computation.Runtime

/-- Starting from base^k, test each actual power and multiply for the next.
The exhausted-fuel result is justified by the refinement theorem's bound. -/
def logarithmLoop (base target : ℕ) : (fuel k current : ℕ) → Traced ℕ
  | 0, k, current => emit .write [k.size,current.size] k
  | fuel+1, k, current =>
      if target ≤ current then
        ⟨k, [⟨.natCompare,[target.size,current.size]⟩,⟨.branch,[1]⟩,⟨.write,[k.size]⟩]⟩
      else
        let next := logarithmLoop base target fuel (k+1) (current*base)
        ⟨next.value,
          [⟨.natCompare,[target.size,current.size]⟩,⟨.branch,[1]⟩,
           ⟨.natAdd,[k.size,1,(k+1).size]⟩,
           ⟨.natMul,[current.size,base.size,(current*base).size]⟩,
           ⟨.recurse,[fuel.size]⟩] ++ next.events⟩

theorem logarithmLoop_value (base target fuel k : ℕ) (base_gt : 1 < base)
    (lower : k ≤ Nat.clog base target) (upper : Nat.clog base target ≤ k+fuel) :
    (logarithmLoop base target fuel k (base^k)).value = Nat.clog base target := by
  induction fuel generalizing k with
  | zero =>
    have equal : k = Nat.clog base target := by omega
    simp [logarithmLoop, emit, equal]
  | succ fuel ih =>
    simp only [logarithmLoop]
    by_cases covered : target ≤ base^k
    · simp only [covered, ↓reduceIte]
      have ceil := (Nat.clog_le_iff_le_pow base_gt).mpr covered
      omega
    · simp only [covered, ↓reduceIte]
      have below : k < Nat.clog base target := (Nat.lt_clog_iff_pow_lt base_gt).mpr (by omega)
      rw [← pow_succ]
      exact ih (k+1) (by omega) (by omega)

theorem logarithmLoop_count (base target fuel k current : ℕ) :
    (logarithmLoop base target fuel k current).events.length ≤ 5*fuel+3 := by
  induction fuel generalizing k current with
  | zero => simp [logarithmLoop, emit]
  | succ fuel ih =>
    simp only [logarithmLoop]
    split
    · simp
    · simp only [List.length_append, List.length_cons, List.length_nil]
      have recursive := ih (k+1) (current*base)
      omega

def ceilingLog (base target fuel : ℕ) : Traced ℕ := logarithmLoop base target fuel 0 1

theorem ceilingLog_value (base target fuel : ℕ) (base_gt : 1 < base)
    (fuel_bound : Nat.clog base target ≤ fuel) :
    (ceilingLog base target fuel).value = Nat.clog base target := by
  simpa only [ceilingLog, pow_zero, zero_add] using
    logarithmLoop_value base target fuel 0 base_gt (Nat.zero_le _) (by simpa using fuel_bound)

theorem helperLog_runtime (h : ℕ) :
    (ceilingLog 2 (8*h) (8*h)).value = Nat.clog 2 (8*h) ∧
    (ceilingLog 2 (8*h) (8*h)).events.length ≤ 40*h+3 := by
  refine ⟨ceilingLog_value _ _ _ (by decide) (helperRepetitions_bound h), ?_⟩
  have count := logarithmLoop_count 2 (8*h) (8*h) 0 1
  dsimp only [ceilingLog]
  omega

theorem gridLog_runtime (h ratio : ℕ) (ratio_ge : 2 ≤ ratio) :
    (ceilingLog ratio (2*ratio*h) (2*h+1)).value = BuyAtBulk.UpperBound.gridDepth h ratio ∧
    (ceilingLog ratio (2*ratio*h) (2*h+1)).events.length ≤ 10*h+8 := by
  refine ⟨ceilingLog_value _ _ _ (by omega) (gridDepth_bound h ratio ratio_ge), ?_⟩
  have bound := logarithmLoop_count ratio (2*ratio*h) (2*h+1) 0 1
  dsimp only [ceilingLog]
  omega

theorem logarithmLoop_words (base target fuel k total : ℕ) (schedule : k+fuel ≤ total) :
    WordsWithin ((base.size+target.size+1)*(total+2)+2)
      (logarithmLoop base target fuel k (base^k)).events := by
  have kbits : k.size ≤ k := Nat.size_le.mpr Nat.lt_two_pow_self
  have powerbits := power_size base k
  induction fuel generalizing k with
  | zero =>
    simp only [logarithmLoop, emit, wordsWithin_cons, wordsWithin_nil, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
    constructor <;> nlinarith
  | succ fuel ih =>
    have fuelbits : fuel.size ≤ fuel := Nat.size_le.mpr Nat.lt_two_pow_self
    have nextbits : (k+1).size ≤ k+1 := Nat.size_le.mpr Nat.lt_two_pow_self
    have nextpower := power_size base (k+1)
    have recursive := ih (k+1) (by omega) nextbits nextpower
    simp only [logarithmLoop]
    split
    · simp only [wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, forall_eq, and_true]
      repeat' apply And.intro
      all_goals nlinarith
    · simp only [wordsWithin_append, ← pow_succ]
      constructor
      · simp only [wordsWithin_cons, wordsWithin_nil, List.mem_cons, List.not_mem_nil,
          or_false, forall_eq_or_imp, forall_eq, and_true]
        repeat' apply And.intro
        all_goals nlinarith
      · exact recursive

/-- Event count and every actual power/counter/input word have polynomial
bounds in the input word lengths and the independently bounded loop fuel. -/
theorem ceilingLog_words (base target fuel : ℕ) :
    WordsWithin ((base.size+target.size+1)*(fuel+2)+2) (ceilingLog base target fuel).events := by
  simpa only [ceilingLog, pow_zero, zero_add] using logarithmLoop_words base target fuel 0 fuel (by omega)

end BuyAtBulk.Computation.Runtime
