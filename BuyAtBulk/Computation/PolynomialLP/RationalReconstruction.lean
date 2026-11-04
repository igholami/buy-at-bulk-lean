import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import BuyAtBulk.Computation.Rational.Encoding
import BuyAtBulk.Computation.PolynomialLP.RationalGap

/-! Rational-native continued fractions. Real approximation theory is used
only in correctness proofs; the data algorithm uses integer/rational floor,
subtraction and reciprocal. Polynomial termination/recovery is developed below. -/
namespace BuyAtBulk.PolynomialLP
open Computation.Rational

def continuedTail (q : ℚ) : ℚ := (Int.fract q)⁻¹

def rationalConvergent : ℚ → ℕ → ℚ
  | q, 0 => ⌊q⌋
  | q, n+1 => ⌊q⌋ + (rationalConvergent (continuedTail q) n)⁻¹

theorem rationalConvergent_eq_real (q : ℚ) (n : ℕ) :
    rationalConvergent q n = Real.convergent (q : ℝ) n := by
  induction n generalizing q with
  | zero => simp [rationalConvergent]
  | succ n ih =>
    rw [rationalConvergent, Real.convergent_succ]
    rw [← Rat.cast_fract, ← Rat.cast_inv, ← ih]
    simp [continuedTail]

theorem fract_num_mod (q : ℚ) : (Int.fract q).num = q.num % (q.den : ℤ) := by
  have positive : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have repr := (div_eq_iff (ne_of_gt positive)).mp q.num_div_den
  have fracrepr : ((Int.fract q).num : ℚ) = Int.fract q * q.den := by
    apply (div_eq_iff (ne_of_gt positive)).mp
    simpa only [Rat.den_intFract] using (Int.fract q).num_div_den
  have equality : ((Int.fract q).num : ℚ) = ((q.num-⌊q⌋*(q.den : ℤ) : ℤ) : ℚ) := by
    rw [fracrepr, Int.fract, sub_mul]
    push_cast
    rw [← repr]
  have integer_equal : (Int.fract q).num = q.num-⌊q⌋*(q.den : ℤ) := by exact_mod_cast equality
  rw [integer_equal, Rat.floor_def', Int.emod_def]
  ring

theorem continuedTail_den (q : ℚ) (nonzero : Int.fract q ≠ 0) :
    (continuedTail q).den = (q.num % (q.den : ℤ)).toNat := by
  rw [continuedTail, Rat.den_inv_of_ne_zero nonzero, fract_num_mod]
  have nonneg : 0 ≤ q.num % (q.den : ℤ) := Int.emod_nonneg _ (by exact_mod_cast q.den_ne_zero)
  exact Int.ofNat_inj.mp ((Int.natAbs_of_nonneg nonneg).trans (Int.toNat_of_nonneg nonneg).symm)

theorem continuedTail_num (q : ℚ) (nonzero : Int.fract q ≠ 0) :
    (continuedTail q).num = (q.den : ℤ) := by
  have positive : (0 : ℚ) < Int.fract q := lt_of_le_of_ne (Int.fract_nonneg q) nonzero.symm
  have numerator : 0 < (Int.fract q).num := Rat.num_pos.mpr positive
  simp [continuedTail, Rat.num_inv, Int.sign_eq_one_of_pos numerator]

theorem continuedTail_den_lt (q : ℚ) (nonzero : Int.fract q ≠ 0) :
    (continuedTail q).den < q.den := by
  rw [continuedTail_den q nonzero]
  have bound : q.num % (q.den : ℤ) < (q.den : ℤ) := Int.emod_lt_of_pos q.num (by exact_mod_cast q.den_pos)
  have nonneg : 0 ≤ q.num % (q.den : ℤ) := Int.emod_nonneg _ (by exact_mod_cast q.den_ne_zero)
  exact_mod_cast (show ((q.num % (q.den : ℤ)).toNat : ℤ) < (q.den : ℤ) by simpa only [Int.toNat_of_nonneg nonneg] using bound)

theorem remainder_twice_lt (d r : ℕ) (positive : 0 < r) (less : r < d) : 2*(d%r) < d := by
  by_cases small : 2*r ≤ d
  · have remainder := Nat.mod_lt d positive
    omega
  · have reduced : d%r = d-r := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [reduced]
    omega

theorem continuedTail_twice_den (q : ℚ) (first : Int.fract q ≠ 0)
    (second : Int.fract (continuedTail q) ≠ 0) :
    2*(continuedTail (continuedTail q)).den < q.den := by
  have denominator : (continuedTail (continuedTail q)).den = q.den%(continuedTail q).den := by
    rw [continuedTail_den _ second, continuedTail_num q first]
    exact (congrArg Int.toNat (Int.natCast_emod q.den (continuedTail q).den)).symm
  rw [denominator]
  exact remainder_twice_lt _ _ (continuedTail q).den_pos (continuedTail_den_lt q first)

theorem rationalConvergent_zero (n : ℕ) : rationalConvergent 0 n = 0 := by
  induction n with
  | zero => simp [rationalConvergent]
  | succ n ih => simpa [rationalConvergent, continuedTail] using ih

theorem floor_tail (q : ℚ) : (⌊q⌋ : ℚ)+(continuedTail q)⁻¹ = q := by
  simpa only [continuedTail, inv_inv] using Int.floor_add_fract q

theorem rationalConvergent_integer (q : ℚ) (integer : Int.fract q = 0) (n : ℕ) :
    rationalConvergent q n = q := by
  have floor : (⌊q⌋ : ℚ) = q := by simpa only [integer, add_zero] using Int.floor_add_fract q
  cases n with
  | zero => simpa only [rationalConvergent] using floor
  | succ n => simp [rationalConvergent, continuedTail, integer, rationalConvergent_zero, floor]

/-- Every two nonterminal continued-fraction steps halve the denominator.
Thus a rational convergent stabilizes after a number of steps linear in the
binary denominator length, rather than in its numerical value. -/
theorem rationalConvergent_stable_aux (k : ℕ) :
    ∀ q : ℚ, q.den < 2^k → ∀ n, 2*k ≤ n → rationalConvergent q n = q := by
  induction k with
  | zero => intro q bound; have positive := q.den_pos; norm_num at bound
  | succ k ih =>
    intro q bound n count
    by_cases integer : Int.fract q = 0
    · exact rationalConvergent_integer q integer n
    by_cases next_integer : Int.fract (continuedTail q) = 0
    · cases n with
      | zero => omega
      | succ n =>
        rw [rationalConvergent, rationalConvergent_integer _ next_integer n]
        exact floor_tail q
    have two := continuedTail_twice_den q integer next_integer
    have shrink : (continuedTail (continuedTail q)).den < 2^k := by
      rw [pow_succ] at bound
      omega
    cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero => omega
      | succ n =>
        rw [rationalConvergent, rationalConvergent, ih _ shrink n (by omega), floor_tail, floor_tail]

theorem rationalConvergent_stable (q : ℚ) (n : ℕ) (long : 2*q.den.size ≤ n) :
    rationalConvergent q n = q :=
  rationalConvergent_stable_aux q.den.size q (Nat.lt_size_self _) n long

/-- Legendre's criterion, with an explicit binary-length search horizon for
our rational-native convergents. No real number is queried by the algorithm. -/
theorem exists_bounded_convergent (approx target : ℚ)
    (close : |approx-target| < 1/(2*(target.den : ℚ)^2)) :
    ∃ n ≤ 2*approx.den.size, rationalConvergent approx n = target := by
  have cast_close : ((|approx-target| : ℚ) : ℝ) < ((1/(2*(target.den : ℚ)^2) : ℚ) : ℝ) := by exact_mod_cast close
  have real_close : |(approx : ℝ)-(target : ℝ)| < 1/(2*(target.den : ℝ)^2) := by
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_mul,
      Rat.cast_ofNat, Rat.cast_pow, Rat.cast_natCast] using cast_close
  obtain ⟨n, equality⟩ := Real.exists_rat_eq_convergent real_close
  rw [← rationalConvergent_eq_real] at equality
  by_cases short : n ≤ 2*approx.den.size
  · exact ⟨n,short,equality.symm⟩
  · have target_eq : target = approx := equality.trans (rationalConvergent_stable approx n (by omega))
    exact ⟨2*approx.den.size,le_rfl,(rationalConvergent_stable approx _ le_rfl).trans target_eq.symm⟩

def reconstructionCandidates (approx : ℚ) : List ℚ :=
  (List.range (2*approx.den.size+1)).map (rationalConvergent approx)

def reconstruct (lo hi : ℚ) (D : ℕ) : Option ℚ :=
  (reconstructionCandidates lo).find? fun q => decide (lo ≤ q ∧ q ≤ hi ∧ q.den ≤ D)

theorem reconstruct_correct (lo hi target : ℚ) (D : ℕ)
    (lower : lo ≤ target) (upper : target ≤ hi) (denominator : target.den ≤ D)
    (narrow : hi-lo < 1/(2*(D : ℚ)^2)) : reconstruct lo hi D = some target := by
  have Dpos : (0 : ℚ) < D := by exact_mod_cast target.den_pos.trans_le denominator
  have target_pos : (0 : ℚ) < target.den := by exact_mod_cast target.den_pos
  have den_le : (target.den : ℚ) ≤ D := by exact_mod_cast denominator
  have comparison : 1/(2*(D : ℚ)^2) ≤ 1/(2*(target.den : ℚ)^2) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have close : |lo-target| < 1/(2*(target.den : ℚ)^2) := by
    rw [abs_of_nonpos (by linarith)]
    exact (show -(lo-target) < 1/(2*(D : ℚ)^2) by linarith).trans_le comparison
  obtain ⟨i, bounded, value⟩ := exists_bounded_convergent lo target close
  have member : target ∈ reconstructionCandidates lo := by
    apply List.mem_map.mpr
    exact ⟨i, List.mem_range.mpr (by omega), value⟩
  have relaxed : hi-lo < 1/((D : ℚ)*D) := by
    apply narrow.trans_le
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  unfold reconstruct
  cases computed : (reconstructionCandidates lo).find? (fun q => decide (lo ≤ q ∧ q ≤ hi ∧ q.den ≤ D)) with
  | none =>
    have impossible := (List.find?_eq_none.mp computed) target member
    exact False.elim (impossible (by simp [lower,upper,denominator]))
  | some found =>
    have passed := List.find?_some computed
    have valid : lo ≤ found ∧ found ≤ hi ∧ found.den ≤ D := of_decide_eq_true passed
    have equal : found = target := by
      rcases lt_trichotomy found target with less | equal | greater
      · have gap := rational_gap found target less D valid.2.2 denominator
        linarith [valid.1]
      · exact equal
      · have gap := rational_gap target found greater D denominator valid.2.2
        linarith [valid.2.1]
    rw [equal]

end BuyAtBulk.PolynomialLP
