import BuyAtBulk.Computation.PolynomialLP.CutData
import Mathlib.Data.Real.Basic
import BuyAtBulk.Computation.Rational.Encoding

/-! Concrete rowwise denominator clearing. All integer quotients are exact;
this transformation performs no optimization and uses no magnitude as fuel. -/
namespace BuyAtBulk.PolynomialLP
open Computation.Rational
open scoped BigOperators
variable {n m : ℕ}

def rowDenominator (row : Vector ℚ n) (bound : ℚ) : ℕ :=
  bound.den*∏ j : Fin n, row[j.val].den

theorem rowDenominator_pos (row : Vector ℚ n) (bound : ℚ) : 0 < rowDenominator row bound :=
  Nat.mul_pos bound.den_pos (Finset.prod_pos (fun j _ => row[j.val].den_pos))

theorem bound_den_dvd (row : Vector ℚ n) (bound : ℚ) : bound.den ∣ rowDenominator row bound :=
  ⟨∏ j : Fin n, row[j.val].den,rfl⟩

theorem row_den_dvd (row : Vector ℚ n) (bound : ℚ) (j : Fin n) :
    row[j.val].den ∣ rowDenominator row bound := by
  have divides : row[j.val].den ∣ ∏ j : Fin n, row[j.val].den :=
    Finset.dvd_prod_of_mem (fun j => row[j.val].den) (Finset.mem_univ j)
  obtain ⟨k,equal⟩ := divides
  refine ⟨bound.den*k,?_⟩
  dsimp only [rowDenominator]
  rw [equal]
  ring

def clearScalar (q : ℚ) (D : ℕ) : ℤ := q.num*(D/q.den : ℕ)

theorem clearScalar_correct (q : ℚ) (D : ℕ) (divides : q.den ∣ D) :
    (clearScalar q D : ℚ) = (D : ℚ)*q := by
  have positive : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have ratio : ((D/q.den : ℕ) : ℚ)*(q.den : ℚ) = (D : ℚ) := by exact_mod_cast Nat.div_mul_cancel divides
  have repr : (q.num : ℚ) = q*(q.den : ℚ) := (div_eq_iff (ne_of_gt positive)).mp q.num_div_den
  simp only [clearScalar,Int.cast_mul,Int.cast_natCast]
  rw [repr]
  calc
    _ = q*(((D/q.den : ℕ) : ℚ)*(q.den : ℚ)) := by ring
    _ = _ := by rw [ratio,mul_comm]

structure IntegerRow (n : ℕ) where
  coefficients : Vector ℤ n
  bound : ℤ

def integerRow (row : Vector ℚ n) (bound : ℚ) : IntegerRow n :=
  let D := rowDenominator row bound
  ⟨row.map (fun q => clearScalar q D),clearScalar bound D⟩

def integerize (input : Stored (n := n) (m := m)) : Stored (n := n) (m := m) :=
  let rows := Vector.ofFn fun i : Fin m => integerRow input.coefficients[i.val] input.bounds[i.val]
  ⟨rows.map (fun row => row.coefficients.map (fun z : ℤ => (z : ℚ))),
    rows.map (fun row => (row.bound : ℚ)),input.objective⟩

theorem integerize_coefficient (input : Stored (n := n) (m := m)) (i : Fin m) (j : Fin n) :
    (integerize input).coefficients[i.val][j.val] =
      (rowDenominator input.coefficients[i.val] input.bounds[i.val] : ℚ)*input.coefficients[i.val][j.val] := by
  simp only [integerize,Vector.getElem_map,Vector.getElem_ofFn,integerRow]
  exact clearScalar_correct _ _ (row_den_dvd _ _ j)

theorem integerize_bound (input : Stored (n := n) (m := m)) (i : Fin m) :
    (integerize input).bounds[i.val] =
      (rowDenominator input.coefficients[i.val] input.bounds[i.val] : ℚ)*input.bounds[i.val] := by
  simp only [integerize,Vector.getElem_map,Vector.getElem_ofFn,integerRow]
  exact clearScalar_correct _ _ (bound_den_dvd _ _)

theorem integerize_feasible (input : Stored (n := n) (m := m)) (x : Fin n → ℚ) :
    (integerize input).problem.Feasible x ↔ input.problem.Feasible x := by
  have scaled (i : Fin m) :
      (integerize input).problem.row i x =
        (rowDenominator input.coefficients[i.val] input.bounds[i.val] : ℚ)*input.problem.row i x := by
    simp only [Stored.problem,rowForm_apply,integerize_coefficient,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  change (∀ i, (integerize input).problem.row i x ≤ (integerize input).problem.bound i) ↔ _
  apply forall_congr'
  intro i
  have bound : (integerize input).problem.bound i =
      (rowDenominator input.coefficients[i.val] input.bounds[i.val] : ℚ)*input.problem.bound i := integerize_bound input i
  rw [scaled i,bound]
  have positive : (0 : ℚ) < rowDenominator input.coefficients[i.val] input.bounds[i.val] := by
    exact_mod_cast rowDenominator_pos input.coefficients[i.val] input.bounds[i.val]
  exact (mul_le_mul_iff_right₀ positive)

def RealFeasible (input : Stored (n := n) (m := m)) (x : Fin n → ℝ) : Prop :=
  ∀ i : Fin m, (∑ j : Fin n, (input.coefficients[i.val][j.val] : ℝ)*x j) ≤ (input.bounds[i.val] : ℝ)

theorem integerize_realFeasible (input : Stored (n := n) (m := m)) (x : Fin n → ℝ) :
    RealFeasible (integerize input) x ↔ RealFeasible input x := by
  unfold RealFeasible
  simp only [integerize_coefficient,integerize_bound,Rat.cast_mul,Rat.cast_natCast]
  simp_rw [mul_assoc,← Finset.mul_sum]
  apply forall_congr'
  intro i
  apply mul_le_mul_iff_right₀
  exact_mod_cast rowDenominator_pos input.coefficients[i.val] input.bounds[i.val]

theorem rowDenominator_bound (row : Vector ℚ n) (bound : ℚ) (L : ℕ)
    (coefficients : ∀ j : Fin n, (Code.ofRat row[j.val]).Bounded L)
    (rhs : (Code.ofRat bound).Bounded L) :
    rowDenominator row bound ≤ 2^((n+1)*L) := by
  have bound_den : bound.den ≤ 2^L := by simpa only [Code.ofRat,Int.natAbs_natCast] using rhs.2.le
  have coeff_den (j : Fin n) : row[j.val].den ≤ 2^L := by
    simpa only [Code.ofRat,Int.natAbs_natCast] using (coefficients j).2.le
  have product : (∏ j : Fin n, row[j.val].den) ≤ 2^(n*L) := by
    calc
      _ ≤ ∏ _j : Fin n, 2^L := Finset.prod_le_prod (fun j _ => coeff_den j)
      _ = _ := by simp [← pow_mul,Nat.mul_comm]
  calc
    rowDenominator row bound ≤ 2^L*2^(n*L) := Nat.mul_le_mul bound_den product
    _ = _ := by rw [← pow_add]; congr 1; ring

theorem clearScalar_bound (q : ℚ) (D L P : ℕ) (positive : 0 < D)
    (input : (Code.ofRat q).Bounded L) (denominator : D ≤ 2^P) :
    (clearScalar q D).natAbs < 2^(L+P) := by
  simp only [clearScalar,Int.natAbs_mul,Int.natAbs_natCast]
  calc
    _ ≤ q.num.natAbs*D := Nat.mul_le_mul_left _ (Nat.div_le_self _ _)
    _ < 2^L*D := mul_lt_mul_of_pos_right input.1 positive
    _ ≤ 2^L*2^P := Nat.mul_le_mul_left _ denominator
    _ = _ := (pow_add _ _ _).symm

theorem integerRow_bounds (row : Vector ℚ n) (bound : ℚ) (L : ℕ)
    (coefficients : ∀ j : Fin n, (Code.ofRat row[j.val]).Bounded L)
    (rhs : (Code.ofRat bound).Bounded L) :
    (∀ j : Fin n, ((integerRow row bound).coefficients[j.val]).natAbs < 2^((n+2)*L)) ∧
      (integerRow row bound).bound.natAbs < 2^((n+2)*L) := by
  have den := rowDenominator_bound row bound L coefficients rhs
  have positive := rowDenominator_pos row bound
  constructor
  · intro j
    have bound := clearScalar_bound row[j.val] _ L _ positive (coefficients j) den
    simpa only [integerRow,Vector.getElem_map,show L+(n+1)*L=(n+2)*L by ring] using bound
  · have bound := clearScalar_bound bound _ L _ positive rhs den
    simpa only [integerRow,show L+(n+1)*L=(n+2)*L by ring] using bound

def inputBudget (input : Stored (n := n) (m := m)) : ℕ :=
  1+((List.finRange m).map fun i => (Code.ofRat input.bounds[i.val]).bits).sum+
    ((List.finRange m).flatMap fun i => (List.finRange n).map fun j => (Code.ofRat input.coefficients[i.val][j.val]).bits).sum+
    ((List.finRange n).map fun j => (Code.ofRat input.objective[j.val]).bits).sum

theorem inputBudget_positive (input : Stored (n := n) (m := m)) : 0 < inputBudget input := by
  unfold inputBudget
  omega

theorem inputBudget_bound (input : Stored (n := n) (m := m)) (i : Fin m) :
    (Code.ofRat input.bounds[i.val]).Bounded (inputBudget input) := by
  have single : (Code.ofRat input.bounds[i.val]).bits ≤ ((List.finRange m).map fun r => (Code.ofRat input.bounds[r.val]).bits).sum :=
    List.single_le_sum (fun x _ => Nat.zero_le x) (Code.ofRat input.bounds[i.val]).bits
    (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩)
  exact Code.bounded_mono (Code.ofRat input.bounds[i.val]).bounded_of_bits
    (by unfold inputBudget; omega)

theorem inputBudget_coefficient (input : Stored (n := n) (m := m)) (i : Fin m) (j : Fin n) :
    (Code.ofRat input.coefficients[i.val][j.val]).Bounded (inputBudget input) := by
  have single : (Code.ofRat input.coefficients[i.val][j.val]).bits ≤
      ((List.finRange m).flatMap fun r => (List.finRange n).map fun c => (Code.ofRat input.coefficients[r.val][c.val]).bits).sum :=
    List.single_le_sum (fun x _ => Nat.zero_le x) (Code.ofRat input.coefficients[i.val][j.val]).bits
    (List.mem_flatMap.mpr ⟨i,List.mem_finRange i,List.mem_map.mpr ⟨j,List.mem_finRange j,rfl⟩⟩)
  exact Code.bounded_mono (Code.ofRat input.coefficients[i.val][j.val]).bounded_of_bits
    (by unfold inputBudget; omega)

def integerA (input : Stored (n := n) (m := m)) (i : Fin m) (j : Fin n) : ℤ :=
  (integerRow input.coefficients[i.val] input.bounds[i.val]).coefficients[j.val]
def integerB (input : Stored (n := n) (m := m)) (i : Fin m) : ℤ :=
  (integerRow input.coefficients[i.val] input.bounds[i.val]).bound

theorem integerize_coefficient_int (input : Stored (n := n) (m := m)) (i : Fin m) (j : Fin n) :
    (integerize input).coefficients[i.val][j.val] = (integerA input i j : ℚ) := by
  simp [integerize,integerA]

theorem integerize_bound_int (input : Stored (n := n) (m := m)) (i : Fin m) :
    (integerize input).bounds[i.val] = (integerB input i : ℚ) := by simp [integerize,integerB]

def integerL (input : Stored (n := n) (m := m)) : ℕ := (n+2)*inputBudget input
def integerH (input : Stored (n := n) (m := m)) : ℕ := 2^(integerL input)

theorem integerA_bound (input : Stored (n := n) (m := m)) (i : Fin m) (j : Fin n) :
    (integerA input i j).natAbs < integerH input :=
  (integerRow_bounds _ _ _ (inputBudget_coefficient input i) (inputBudget_bound input i)).1 j

theorem integerB_bound (input : Stored (n := n) (m := m)) (i : Fin m) :
    (integerB input i).natAbs < integerH input :=
  (integerRow_bounds _ _ _ (inputBudget_coefficient input i) (inputBudget_bound input i)).2

theorem integerH_positive (input : Stored (n := n) (m := m)) : 0 < integerH input := by
  unfold integerH
  positivity

theorem integerH_bits (input : Stored (n := n) (m := m)) :
    (integerH input).size = integerL input+1 := Nat.size_pow

theorem boxed_coefficient_integral (input : Stored (n := n) (m := m)) :
    ∀ (i : Fin (m+(n+n))) (j : Fin n),
      ((integerize input).boxed.coefficients[i.val][j.val]).den=1 ∧
      ((integerize input).boxed.coefficients[i.val][j.val]).num.natAbs ≤ integerH input := by
  have one : 1 ≤ integerH input := integerH_positive input
  intro i
  apply Fin.addCases (motive:=fun i => ∀ j : Fin n,
    ((integerize input).boxed.coefficients[i.val][j.val]).den=1 ∧
      ((integerize input).boxed.coefficients[i.val][j.val]).num.natAbs ≤ integerH input) _ _ i
  · intro i j
    have bound := (integerA_bound input i j).le
    simpa [Stored.boxed,Stored.extend,integerize_coefficient_int] using (And.intro rfl bound : (1 : ℕ)=1 ∧ _)
  · intro k
    apply Fin.addCases (motive:=fun k => ∀ j : Fin n,
      ((integerize input).boxed.coefficients[(Fin.natAdd m k).val][j.val]).den=1 ∧
        ((integerize input).boxed.coefficients[(Fin.natAdd m k).val][j.val]).num.natAbs ≤ integerH input) _ _ k
    · intro i j
      by_cases same : i=j <;> simp [Stored.boxed,Stored.extend,coordinateRows,same,one]
    · intro i j
      by_cases same : i=j <;> simp [Stored.boxed,Stored.extend,coordinateRows,same,one]

theorem boxed_bound_integral (input : Stored (n := n) (m := m)) :
    ∀ i : Fin (m+(n+n)), ((integerize input).boxed.bounds[i.val]).den=1 ∧
      ((integerize input).boxed.bounds[i.val]).num.natAbs ≤ integerH input := by
  have one : 1 ≤ integerH input := integerH_positive input
  intro i
  apply Fin.addCases (motive:=fun i => ((integerize input).boxed.bounds[i.val]).den=1 ∧
      ((integerize input).boxed.bounds[i.val]).num.natAbs ≤ integerH input) _ _ i
  · intro i
    have bound := (integerB_bound input i).le
    simpa [Stored.boxed,Stored.extend,integerize_bound_int] using (And.intro rfl bound : (1 : ℕ)=1 ∧ _)
  · intro k
    apply Fin.addCases (motive:=fun k => ((integerize input).boxed.bounds[(Fin.natAdd m k).val]).den=1 ∧
      ((integerize input).boxed.bounds[(Fin.natAdd m k).val]).num.natAbs ≤ integerH input) _ _ k
    · intro i
      simp [Stored.boxed,Stored.extend,one]
    · intro i
      simp [Stored.boxed,Stored.extend,one]

/-- All integer witnesses are actual normalized numerators of the computed
stored boxed table. No choice or assumed integrality certificate is used. -/
theorem boxed_integer_data (input : Stored (n := n) (m := m)) :
    (∀ (i : Fin (m+(n+n))) (j : Fin n), (integerize input).boxed.coefficients[i.val][j.val] =
      (((integerize input).boxed.coefficients[i.val][j.val]).num : ℚ)) ∧
    (∀ i : Fin (m+(n+n)), (integerize input).boxed.bounds[i.val] = (((integerize input).boxed.bounds[i.val]).num : ℚ)) ∧
    (∀ (i : Fin (m+(n+n))) (j : Fin n), (((integerize input).boxed.coefficients[i.val][j.val]).num).natAbs ≤ integerH input) ∧
    (∀ i : Fin (m+(n+n)), (((integerize input).boxed.bounds[i.val]).num).natAbs ≤ integerH input) := by
  refine ⟨?_,?_,fun i j => (boxed_coefficient_integral input i j).2,fun i => (boxed_bound_integral input i).2⟩
  · intro i j
    have encoded := ((integerize input).boxed.coefficients[i.val][j.val]).num_div_den
    rw [(boxed_coefficient_integral input i j).1,Nat.cast_one,div_one] at encoded
    exact encoded.symm
  · intro i
    have encoded := ((integerize input).boxed.bounds[i.val]).num_div_den
    rw [(boxed_bound_integral input i).1,Nat.cast_one,div_one] at encoded
    exact encoded.symm

end BuyAtBulk.PolynomialLP
