import BuyAtBulk.Computation.Runtime.Primitive
import BuyAtBulk.Model.RationalLP.Problem
import BuyAtBulk.Computation.HelperExpressions
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Fin

/-! Exact separation on an explicitly stored rational inequality system.
This is a proved subroutine, not a polynomial-time LP optimizer. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP
open Computation Computation.Runtime
variable {n m : ℕ}

/-- Entries are normalized binary rationals; vectors supply the entire input,
rather than arbitrary coefficient callbacks with unspecified running costs. -/
structure Stored where
  coefficients : Vector (Vector ℚ n) m
  bounds : Vector ℚ m
  objective : Vector ℚ n

def rowForm (coefficients : Vector ℚ n) : (Fin n → ℚ) →ₗ[ℚ] ℚ :=
  ∑ j : Fin n, coefficients[j.val] • LinearMap.proj j

@[simp] theorem rowForm_apply (coefficients : Vector ℚ n) (x : Fin n → ℚ) :
    rowForm coefficients x = ∑ j, coefficients[j.val] * x j := by
  simp only [rowForm, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]

def Stored.problem (input : Stored (n := n) (m := m)) : RationalLP.Problem (Fin n) (Fin m) where
  row i := rowForm input.coefficients[i.val]
  bound i := input.bounds[i.val]
  objective := rowForm input.objective

def dotScan (a x : Vector ℚ n) : List (Fin n) → Traced ℚ
  | [] => Traced.pure 0
  | j :: rest => do
      let _ ← emit .scan [j.val.size] ()
      let coefficient ← readRat a j
      let coordinate ← readRat x j
      let term ← ratMul coefficient coordinate
      let tail ← dotScan a x rest
      ratAdd term tail

theorem dotScan_value (a x : Vector ℚ n) (indices : List (Fin n)) :
    (dotScan a x indices).value = (indices.map fun j => a[j.val] * x[j.val]).sum := by
  induction indices with
  | nil => rfl
  | cons j rest ih =>
    simp only [dotScan, Traced.bind_value, emit_value, readRat, ratMul_value, ratAdd_value,
      ih, List.map_cons, List.sum_cons]

theorem dotScan_count (a x : Vector ℚ n) (indices : List (Fin n)) :
    (dotScan a x indices).events.length = 7 * indices.length := by
  induction indices with
  | nil => rfl
  | cons j rest ih =>
    simp only [dotScan, Traced.bind_events, Traced.bind_value, emit_value, readRat, List.length_append,
      emit_length, ratMul_length, ratAdd_length, ih, List.length_cons]
    omega

def dot (a x : Vector ℚ n) : Traced ℚ := dotScan a x (List.finRange n)

theorem dot_value (a x : Vector ℚ n) :
    (dot a x).value = rowForm a (fun j => x[j.val]) := by
  rw [dot, dotScan_value, rowForm_apply, Fin.sum_univ_def]

@[simp] theorem dot_count (a x : Vector ℚ n) : (dot a x).events.length = 7 * n := by
  simp only [dot, dotScan_count, List.length_finRange]

def violated (input : Stored (n := n) (m := m)) (x : Vector ℚ n) (i : Fin m) : Traced Bool := do
  let a ← emit .read [i.val.size] input.coefficients[i.val]
  let value ← dot a x
  let bound ← readRat input.bounds i
  ratLess bound value

theorem violated_value (input : Stored (n := n) (m := m)) (x : Vector ℚ n) (i : Fin m) :
    (violated input x i).value = decide (input.problem.bound i < input.problem.row i (fun j => x[j.val])) := by
  simp only [violated, Traced.bind_value, emit_value, dot_value, readRat, ratLess, Stored.problem]

@[simp] theorem violated_count (input : Stored (n := n) (m := m)) (x : Vector ℚ n) (i : Fin m) :
    (violated input x i).events.length = 7 * n + 3 := by
  simp only [violated, Traced.bind_events, Traced.bind_value, emit_value, List.length_append,
    emit_length, dot_count, readRat, ratLess]
  omega

def separationScan (input : Stored (n := n) (m := m)) (x : Vector ℚ n) : List (Fin m) → Traced (Option (Fin m))
  | [] => Traced.pure none
  | i :: rest => do
      let _ ← emit .scan [i.val.size] ()
      let test ← violated input x i
      let test ← branch test
      if test then Traced.pure (some i) else separationScan input x rest

theorem separationScan_none (input : Stored (n := n) (m := m)) (x : Vector ℚ n) (indices : List (Fin m)) :
    (separationScan input x indices).value = none ↔
      ∀ i ∈ indices, input.problem.row i (fun j => x[j.val]) ≤ input.problem.bound i := by
  induction indices with
  | nil => simp [separationScan, Traced.pure]
  | cons i rest ih =>
    simp only [separationScan, Traced.bind_value, emit_value, violated_value, branch,
      Traced.ite_value, Traced.pure_value, decide_eq_true_eq, List.mem_cons, forall_eq_or_imp, ih]
    by_cases test : input.problem.bound i < input.problem.row i (fun j => x[j.val])
    · simp only [if_pos test, Option.some_ne_none, false_iff, not_and]
      exact fun bounded => (not_le_of_gt test bounded).elim
    · simp only [if_neg test]
      rw [ih]
      exact (and_iff_right (not_lt.mp test)).symm

theorem separationScan_some (input : Stored (n := n) (m := m)) (x : Vector ℚ n) (indices : List (Fin m))
    (i : Fin m) (returned : (separationScan input x indices).value = some i) :
    i ∈ indices ∧ input.problem.bound i < input.problem.row i (fun j => x[j.val]) := by
  induction indices with
  | nil => simp [separationScan, Traced.pure] at returned
  | cons j rest ih =>
    simp only [separationScan, Traced.bind_value, emit_value, violated_value, branch,
      Traced.ite_value, Traced.pure_value, decide_eq_true_eq] at returned
    split_ifs at returned with test
    · have equal := Option.some.inj returned
      subst j
      exact ⟨by simp, test⟩
    · obtain ⟨member, violation⟩ := ih returned
      exact ⟨by simp [member], violation⟩

theorem separationScan_count (input : Stored (n := n) (m := m)) (x : Vector ℚ n) (indices : List (Fin m)) :
    (separationScan input x indices).events.length ≤ (7 * n + 5) * indices.length := by
  induction indices with
  | nil => simp [separationScan, Traced.pure]
  | cons i rest ih =>
    simp only [separationScan, Traced.bind_events, Traced.bind_value, List.length_append,
      emit_length, violated_count, branch, emit_value]
    simp only [Traced.ite_events]
    split_ifs <;> simp_all only [Traced.pure_events, List.length_nil, List.length_cons, emit_length] <;> nlinarith

def separate (input : Stored (n := n) (m := m)) (x : Vector ℚ n) : Traced (Option (Fin m)) :=
  separationScan input x (List.finRange m)

/-- Either membership is verified, or the returned stored row strictly
separates the query from every feasible point of the rational LP. -/
theorem separate_correct (input : Stored (n := n) (m := m)) (x : Vector ℚ n) :
    match (separate input x).value with
    | none => input.problem.Feasible (fun j => x[j.val])
    | some i => ∀ y, input.problem.Feasible y →
        input.problem.row i y ≤ input.problem.bound i ∧
        input.problem.bound i < input.problem.row i (fun j => x[j.val]) := by
  cases returned : (separate input x).value with
  | none =>
    exact fun i => (separationScan_none input x _).mp returned i (List.mem_finRange i)
  | some i =>
    have violation := (separationScan_some input x _ i returned).2
    exact fun y feasible => ⟨feasible i, violation⟩

theorem separate_count (input : Stored (n := n) (m := m)) (x : Vector ℚ n) :
    (separate input x).events.length ≤ (7 * n + 5) * m := by
  simpa only [separate, List.length_finRange] using separationScan_count input x (List.finRange m)

/-- Normalized dot-product output has polynomial binary length in the input
word bound. This is not yet a bound on every event in a solver trace. -/
theorem dot_output_bits (a x : Vector ℚ n) (L : ℕ) (constant : 5 ≤ L)
    (a_bits : ∀ j : Fin n, (Rational.Code.ofRat a[j.val]).bits + 1 ≤ L)
    (x_bits : ∀ j : Fin n, (Rational.Code.ofRat x[j.val]).bits + 1 ≤ L) :
    (Rational.Code.ofRat (dot a x).value).bits ≤ 2 * (4 * n + 1) * L + 2 := by
  let terms := (List.finRange n).map fun j => (a[j.val], x[j.val])
  have bounded := HelperExpressions.sum_products_bits terms L constant (by
    intro q member
    obtain ⟨j, _, equal⟩ := List.mem_map.mp member
    subst q
    exact ⟨a_bits j, x_bits j⟩)
  simpa only [terms, dot, dotScan_value, List.map_map, Function.comp_def, List.length_map,
    List.length_finRange] using bounded

end BuyAtBulk.PolynomialLP
