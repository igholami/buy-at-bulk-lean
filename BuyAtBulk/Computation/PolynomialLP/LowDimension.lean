import BuyAtBulk.Computation.PolynomialLP.Separation

/-! Exact zero- and one-dimensional bounded LP solvers. The unary solver
intersects rational halfspaces and selects the objective-minimizing endpoint;
it does not enumerate vertices or assume an optimum certificate. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP
variable {m : ℕ}

structure Interval where
  lower : ℚ
  upper : ℚ

def Interval.Contains (interval : Interval) (x : ℚ) : Prop := interval.lower ≤ x ∧ x ≤ interval.upper

def Interval.cut (interval : Interval) (a b : ℚ) : Interval :=
  if a = 0 then if 0 ≤ b then interval else ⟨1, 0⟩ else
    if 0 < a then ⟨interval.lower, min interval.upper (b / a)⟩ else
      ⟨max interval.lower (b / a), interval.upper⟩

theorem Interval.cut_contains (interval : Interval) (a b x : ℚ) :
    (interval.cut a b).Contains x ↔ interval.Contains x ∧ a * x ≤ b := by
  by_cases zero : a = 0
  · subst a
    by_cases bound : 0 ≤ b
    · simp [Interval.cut, bound, Interval.Contains]
    · have cut_eq : interval.cut 0 b = ⟨1, 0⟩ := by simp [Interval.cut, bound]
      rw [cut_eq]
      dsimp only [Interval.Contains]
      simp only [zero_mul]
      constructor
      · rintro ⟨lower, upper⟩
        linarith
      · rintro ⟨_, impossible⟩
        exact (bound impossible).elim
  · by_cases positive : 0 < a
    · have row : a * x ≤ b ↔ x ≤ b / a := by rw [le_div_iff₀ positive, mul_comm]
      simp only [Interval.cut, if_neg zero, if_pos positive, Interval.Contains, le_min_iff, row, and_assoc]
    · have negative : a < 0 := lt_of_le_of_ne (not_lt.mp positive) zero
      have row : a * x ≤ b ↔ b / a ≤ x := by rw [div_le_iff_of_neg' negative]
      simp only [Interval.cut, if_neg zero, if_neg positive, Interval.Contains, max_le_iff, row]
      tauto

def intervalScan (input : Stored (n := 1) (m := m)) : List (Fin m) → Interval → Interval
  | [], interval => interval
  | i :: rest, interval => intervalScan input rest (interval.cut input.coefficients[i.val][0] input.bounds[i.val])

theorem intervalScan_contains (input : Stored (n := 1) (m := m)) (indices : List (Fin m))
    (interval : Interval) (x : ℚ) :
    (intervalScan input indices interval).Contains x ↔
      interval.Contains x ∧ ∀ i ∈ indices, input.coefficients[i.val][0] * x ≤ input.bounds[i.val] := by
  induction indices generalizing interval with
  | nil => simp [intervalScan]
  | cons i rest ih =>
    rw [intervalScan, ih, Interval.cut_contains]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

def unaryInterval (input : Stored (n := 1) (m := m)) : Interval := intervalScan input (List.finRange m) ⟨0, 1⟩

theorem unaryInterval_contains (input : Stored (n := 1) (m := m)) (x : ℚ) :
    (unaryInterval input).Contains x ↔ 0 ≤ x ∧ x ≤ 1 ∧ input.problem.Feasible (fun _ => x) := by
  rw [unaryInterval, intervalScan_contains]
  simp only [Interval.Contains, List.mem_finRange, forall_true_left, Stored.problem,
    RationalLP.Problem.Feasible, rowForm_apply, Fin.sum_univ_one, Fin.val_zero]
  tauto

def unarySolve (input : Stored (n := 1) (m := m)) : Option ℚ :=
  let interval := unaryInterval input
  if interval.lower ≤ interval.upper then
    some (if input.objective[0] < 0 then interval.upper else interval.lower)
  else none

theorem unarySolve_some (input : Stored (n := 1) (m := m)) (point : ℚ)
    (computed : unarySolve input = some point) :
    input.problem.Feasible (fun _ => point) ∧
      ∀ y : Fin 1 → ℚ, input.problem.Feasible y → (∀ j, 0 ≤ y j ∧ y j ≤ 1) →
        input.problem.objective (fun _ => point) ≤ input.problem.objective y := by
  let interval := unaryInterval input
  have selected : interval.lower ≤ interval.upper ∧
      point = if input.objective[0] < 0 then interval.upper else interval.lower := by
    change (if interval.lower ≤ interval.upper then
      some (if input.objective[0] < 0 then interval.upper else interval.lower) else none) = some point at computed
    by_cases valid : interval.lower ≤ interval.upper
    · have equality : some (if input.objective[0] < 0 then interval.upper else interval.lower) = some point := by
        simpa only [if_pos valid] using computed
      exact ⟨valid, (Option.some.inj equality).symm⟩
    · have impossible : (none : Option ℚ) = some point := by
        simpa only [if_neg valid] using computed
      cases impossible
  have supported : interval.Contains point := by
    rw [selected.2]
    split_ifs
    · exact ⟨selected.1, le_rfl⟩
    · exact ⟨le_rfl, selected.1⟩
  refine ⟨((unaryInterval_contains input point).mp supported).2.2, ?_⟩
  intro y feasible box
  have constant : y = fun _ => y 0 := by ext j; congr 1; exact Subsingleton.elim _ _
  have member : interval.Contains (y 0) := by
    apply (unaryInterval_contains input (y 0)).mpr
    exact ⟨(box 0).1, (box 0).2, by simpa only [← constant] using feasible⟩
  change (rowForm input.objective) (fun _ => point) ≤ (rowForm input.objective) y
  rw [constant, rowForm_apply, rowForm_apply]
  simp only [Fin.sum_univ_one, Fin.val_zero]
  rw [selected.2]
  split_ifs with negative
  · exact mul_le_mul_of_nonpos_left member.2 negative.le
  · exact mul_le_mul_of_nonneg_left member.1 (not_lt.mp negative)

theorem unarySolve_none (input : Stored (n := 1) (m := m))
    (cube : input.problem.InUnitCube) (computed : unarySolve input = none) :
    ¬∃ x, input.problem.Feasible x := by
  rintro ⟨x, feasible⟩
  have constant : x = fun _ => x 0 := by ext j; congr 1; exact Subsingleton.elim _ _
  have member : (unaryInterval input).Contains (x 0) := by
    apply (unaryInterval_contains input (x 0)).mpr
    exact ⟨(cube x feasible 0).1, (cube x feasible 0).2, by simpa only [← constant] using feasible⟩
  have valid := member.1.trans member.2
  simp only [unarySolve, if_pos valid, Option.some_ne_none] at computed

def zeroSolve (input : Stored (n := 0) (m := m)) : Option (Vector ℚ 0) :=
  match (separate input (Vector.replicate 0 0)).value with
  | none => some (Vector.replicate 0 0)
  | some _ => none

theorem zeroSolve_correct (input : Stored (n := 0) (m := m)) :
    match zeroSolve input with
    | none => ¬∃ x, input.problem.Feasible x
    | some point => input.problem.Feasible (fun j => point[j.val]) ∧
        ∀ y, input.problem.Feasible y → input.problem.objective (fun j => point[j.val]) ≤ input.problem.objective y := by
  unfold zeroSolve
  cases separated : (separate input (Vector.replicate 0 0)).value with
  | none =>
    have correct := separate_correct input (Vector.replicate 0 0)
    simp only [separated] at correct ⊢
    exact ⟨correct, fun y _ => by simp [Stored.problem, rowForm_apply]⟩
  | some i =>
    have correct := separate_correct input (Vector.replicate 0 0)
    simp only [separated] at correct ⊢
    rintro ⟨y, feasible⟩
    obtain ⟨bound, strict⟩ := correct y feasible
    have equal : y = fun j => (Vector.replicate 0 (0 : ℚ))[j.val] := funext fun j => j.elim0
    rw [equal] at bound
    exact (not_lt_of_ge bound) strict

end BuyAtBulk.PolynomialLP
