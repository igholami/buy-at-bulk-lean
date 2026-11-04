import BuyAtBulk.Computation.Rational.Expression
import BuyAtBulk.Computation.HelperExpressions
import BuyAtBulk.Computation.HelperChoose

/-! Instruction-level evaluation of the helper's unreduced expression trees.
Events contain the actual signed integers, including the two temporary cross
products of addition. This does not include expression construction or helper
coefficient construction; those have separate traces. -/
namespace BuyAtBulk.Computation.Runtime.RawExpression
open Rational

inductive Operation where
  | read | write | add | mul | neg | equal | less | le | branch | dispatch | pair
  deriving DecidableEq, Repr

structure Event where
  operation : Operation
  values : List ℤ
  deriving Repr

structure Result (α : Type) where
  value : α
  events : List Event

def event (op : Operation) (values : List ℤ) : Event := ⟨op, values⟩
def readCode (q : Code) : List Event := [event .read [q.numerator, q.denominator]]
def writeCode (q : Code) : List Event := [event .write [q.numerator, q.denominator]]

def add (q r : Code) : Result Code :=
  let a := q.numerator * r.denominator
  let b := r.numerator * q.denominator
  let c := a + b
  let d := q.denominator * r.denominator
  ⟨⟨c, d, mul_ne_zero q.denominator_ne r.denominator_ne⟩,
    readCode q ++ readCode r ++
    [event .mul [q.numerator, r.denominator, a],
     event .mul [r.numerator, q.denominator, b], event .add [a, b, c],
     event .mul [q.denominator, r.denominator, d], event .pair [c, d]]⟩

def mul (q r : Code) : Result Code :=
  let a := q.numerator * r.numerator
  let b := q.denominator * r.denominator
  ⟨⟨a, b, mul_ne_zero q.denominator_ne r.denominator_ne⟩,
    readCode q ++ readCode r ++
    [event .mul [q.numerator, r.numerator, a],
     event .mul [q.denominator, r.denominator, b], event .pair [a, b]]⟩

def neg (q : Code) : Result Code :=
  ⟨q.neg, readCode q ++ [event .neg [q.numerator, -q.numerator],
    event .pair [-q.numerator, q.denominator]]⟩

def inv (q : Code) : Result Code :=
  if zero : q.numerator = 0 then
    ⟨Code.zero, readCode q ++ [event .equal [q.numerator, 0], event .branch [1], event .pair [0, 1]]⟩
  else
    ⟨⟨q.denominator, q.numerator, zero⟩,
      readCode q ++ [event .equal [q.numerator, 0], event .branch [0],
        event .pair [q.denominator, q.numerator]]⟩

@[simp] theorem add_value (q r : Code) : (add q r).value = q.add r := rfl
@[simp] theorem mul_value (q r : Code) : (mul q r).value = q.mul r := rfl
@[simp] theorem neg_value (q : Code) : (neg q).value = q.neg := rfl
@[simp] theorem inv_value (q : Code) : (inv q).value = q.inv := by
  unfold inv Code.inv
  split_ifs <;> rfl
@[simp] theorem add_length (q r : Code) : (add q r).events.length = 7 := rfl
@[simp] theorem mul_length (q r : Code) : (mul q r).events.length = 5 := rfl
@[simp] theorem neg_length (q : Code) : (neg q).events.length = 3 := rfl
@[simp] theorem inv_length (q : Code) : (inv q).events.length = 4 := by
  unfold inv
  split_ifs <;> rfl

def evaluate : Expr → Result Code
  | .literal q => ⟨q, [event .dispatch [0]] ++ readCode q ++ writeCode q⟩
  | .add a b =>
      let left := evaluate a
      let right := evaluate b
      let result := add left.value right.value
      ⟨result.value, [event .dispatch [1]] ++ left.events ++ right.events ++ result.events ++ writeCode result.value⟩
  | .mul a b =>
      let left := evaluate a
      let right := evaluate b
      let result := mul left.value right.value
      ⟨result.value, [event .dispatch [2]] ++ left.events ++ right.events ++ result.events ++ writeCode result.value⟩
  | .neg a =>
      let child := evaluate a
      let result := neg child.value
      ⟨result.value, [event .dispatch [3]] ++ child.events ++ result.events ++ writeCode result.value⟩
  | .inv a =>
      let child := evaluate a
      let result := inv child.value
      ⟨result.value, [event .dispatch [4]] ++ child.events ++ result.events ++ writeCode result.value⟩

@[simp] theorem evaluate_value (e : Expr) : (evaluate e).value = e.evaluate.1 := by
  induction e <;> simp_all [evaluate, Expr.evaluate]

theorem evaluate_length (e : Expr) : (evaluate e).events.length ≤ 10 * e.treeSize := by
  induction e with
  | literal q => simp [evaluate, readCode, writeCode, Expr.treeSize]
  | add a b ha hb =>
    simp only [evaluate, List.length_append, List.length_singleton, add_length, writeCode] at *
    simp only [List.length_singleton, Expr.treeSize]
    omega
  | mul a b ha hb =>
    simp only [evaluate, List.length_append, List.length_singleton, mul_length, writeCode] at *
    simp only [List.length_singleton, Expr.treeSize]
    omega
  | neg a ha =>
    simp only [evaluate, List.length_append, List.length_singleton, neg_length, writeCode] at *
    simp only [List.length_singleton, Expr.treeSize]
    omega
  | inv a ha =>
    simp only [evaluate, List.length_append, List.length_singleton, inv_length, writeCode] at *
    simp only [List.length_singleton, Expr.treeSize]
    omega

/-- Every actual operand, temporary result and stored result fits this bound. -/
def EventsBounded (events : List Event) (k : ℕ) : Prop :=
  ∀ entry ∈ events, ∀ z ∈ entry.values, z.natAbs < 2 ^ k

theorem events_mono {events : List Event} {k l : ℕ}
    (bound : EventsBounded events k) (le : k ≤ l) : EventsBounded events l := by
  intro entry member z value
  exact (bound entry member z value).trans_le (Nat.pow_le_pow_right (by decide) le)

theorem events_append {a b : List Event} {k : ℕ} :
    EventsBounded (a ++ b) k ↔ EventsBounded a k ∧ EventsBounded b k := by
  constructor
  · intro bound
    exact ⟨fun entry member => bound entry (List.mem_append_left _ member),
      fun entry member => bound entry (List.mem_append_right _ member)⟩
  · rintro ⟨left, right⟩ entry member
    rcases List.mem_append.mp member with member | member
    · exact left entry member
    · exact right entry member

theorem events_single {entry : Event} {k : ℕ} :
    EventsBounded [entry] k ↔ ∀ z ∈ entry.values, z.natAbs < 2 ^ k := by
  simp [EventsBounded]

private theorem product_bound {a b : ℤ} {k l : ℕ}
    (ha : a.natAbs < 2 ^ k) (hb : b.natAbs < 2 ^ l) :
    (a * b).natAbs < 2 ^ (k + l) := by
  rw [Int.natAbs_mul, pow_add]
  exact (Nat.mul_le_mul_left a.natAbs hb.le).trans_lt
    (mul_lt_mul_of_pos_right ha (by positivity))

theorem read_bounded {q : Code} {k : ℕ} (bound : q.Bounded k) : EventsBounded (readCode q) k := by
  simpa [EventsBounded, readCode, event, Code.Bounded] using bound

theorem write_bounded {q : Code} {k : ℕ} (bound : q.Bounded k) : EventsBounded (writeCode q) k := by
  simpa [EventsBounded, writeCode, event, Code.Bounded] using bound

theorem add_bounded {q r : Code} {k l : ℕ} (hq : q.Bounded k) (hr : r.Bounded l) :
    EventsBounded (add q r).events (k + l + 3) := by
  have qbound := Code.bounded_mono hq (show k ≤ k + l + 3 by omega)
  have rbound := Code.bounded_mono hr (show l ≤ k + l + 3 by omega)
  have abound := Code.bounded_mono (Code.add_bounded hq hr) (show k + l + 1 ≤ k + l + 3 by omega)
  have prod1 := (product_bound hq.1 hr.2).trans_le
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show k + l ≤ k + l + 3 by omega))
  have prod2 := (product_bound hr.1 hq.2).trans_le
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show l + k ≤ k + l + 3 by omega))
  have prod3 := (product_bound hq.2 hr.2).trans_le
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show k + l ≤ k + l + 3 by omega))
  rcases qbound with ⟨qn, qd⟩
  rcases rbound with ⟨rn, rd⟩
  rcases abound with ⟨an, ad⟩
  simpa [EventsBounded, add, readCode, event] using
    (show (q.numerator.natAbs < 2 ^ (k+l+3) ∧ q.denominator.natAbs < 2 ^ (k+l+3)) ∧
      (r.numerator.natAbs < 2 ^ (k+l+3) ∧ r.denominator.natAbs < 2 ^ (k+l+3)) ∧
      (q.numerator.natAbs < 2 ^ (k+l+3) ∧ r.denominator.natAbs < 2 ^ (k+l+3) ∧
        (q.numerator*r.denominator).natAbs < 2 ^ (k+l+3)) ∧
      (r.numerator.natAbs < 2 ^ (k+l+3) ∧ q.denominator.natAbs < 2 ^ (k+l+3) ∧
        (r.numerator*q.denominator).natAbs < 2 ^ (k+l+3)) ∧
      ((q.numerator*r.denominator).natAbs < 2 ^ (k+l+3) ∧
        (r.numerator*q.denominator).natAbs < 2 ^ (k+l+3) ∧
        (q.numerator*r.denominator+r.numerator*q.denominator).natAbs < 2 ^ (k+l+3)) ∧
      (q.denominator.natAbs < 2 ^ (k+l+3) ∧ r.denominator.natAbs < 2 ^ (k+l+3) ∧
        (q.denominator*r.denominator).natAbs < 2 ^ (k+l+3)) ∧
      ((q.numerator*r.denominator+r.numerator*q.denominator).natAbs < 2 ^ (k+l+3) ∧
        (q.denominator*r.denominator).natAbs < 2 ^ (k+l+3)) from
      ⟨⟨qn,qd⟩,⟨rn,rd⟩,⟨qn,rd,prod1⟩,⟨rn,qd,prod2⟩,⟨prod1,prod2,an⟩,⟨qd,rd,prod3⟩,⟨an,ad⟩⟩)

theorem mul_bounded {q r : Code} {k l : ℕ} (hq : q.Bounded k) (hr : r.Bounded l) :
    EventsBounded (mul q r).events (k + l + 3) := by
  have qbound := Code.bounded_mono hq (show k ≤ k + l + 3 by omega)
  have rbound := Code.bounded_mono hr (show l ≤ k + l + 3 by omega)
  have result := Code.bounded_mono (Code.mul_bounded hq hr) (show k + l ≤ k + l + 3 by omega)
  rcases qbound with ⟨qn, qd⟩
  rcases rbound with ⟨rn, rd⟩
  rcases result with ⟨an, ad⟩
  simpa [EventsBounded, mul, readCode, event] using
    (show (q.numerator.natAbs < 2 ^ (k+l+3) ∧ q.denominator.natAbs < 2 ^ (k+l+3)) ∧
      (r.numerator.natAbs < 2 ^ (k+l+3) ∧ r.denominator.natAbs < 2 ^ (k+l+3)) ∧
      (q.numerator.natAbs < 2 ^ (k+l+3) ∧ r.numerator.natAbs < 2 ^ (k+l+3) ∧
        (q.numerator*r.numerator).natAbs < 2 ^ (k+l+3)) ∧
      (q.denominator.natAbs < 2 ^ (k+l+3) ∧ r.denominator.natAbs < 2 ^ (k+l+3) ∧
        (q.denominator*r.denominator).natAbs < 2 ^ (k+l+3)) ∧
      ((q.numerator*r.numerator).natAbs < 2 ^ (k+l+3) ∧
        (q.denominator*r.denominator).natAbs < 2 ^ (k+l+3)) from
      ⟨⟨qn,qd⟩,⟨rn,rd⟩,⟨qn,rn,an⟩,⟨qd,rd,ad⟩,⟨an,ad⟩⟩)

theorem neg_bounded {q : Code} {k : ℕ} (hq : q.Bounded k) :
    EventsBounded (neg q).events (k + 3) := by
  have bound := Code.bounded_mono hq (show k ≤ k+3 by omega)
  simpa [EventsBounded, neg, readCode, event] using
    (show (q.numerator.natAbs < 2^(k+3) ∧ q.denominator.natAbs < 2^(k+3)) ∧
      (q.numerator.natAbs < 2^(k+3) ∧ q.numerator.natAbs < 2^(k+3)) ∧
      (q.numerator.natAbs < 2^(k+3) ∧ q.denominator.natAbs < 2^(k+3)) from
      ⟨bound, ⟨bound.1,bound.1⟩, bound⟩)

theorem inv_bounded {q : Code} {k : ℕ} (hq : q.Bounded k) :
    EventsBounded (inv q).events (k + 3) := by
  have bound := Code.bounded_mono hq (show k ≤ k+3 by omega)
  have one : (1 : ℕ) < 2^(k+3) := Nat.one_lt_pow (by omega) (by decide)
  have zero : (0 : ℕ) < 2^(k+3) := by positivity
  unfold inv
  split_ifs <;> simp [EventsBounded, readCode, event, bound.1, bound.2, one, zero]

theorem dispatch_bounded (tag : ℕ) (small : tag ≤ 4) (k : ℕ) :
    EventsBounded [event .dispatch [(tag : ℤ)]] (k + 3) := by
  apply events_single.mpr
  intro z member
  have equal : z = (tag : ℤ) := by simpa [event] using member
  subst z
  simp only [Int.natAbs_natCast]
  have lower : (8 : ℕ) ≤ 2 ^ (k+3) := by
    calc
      _ = 2^3 := by decide
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem evaluate_bounded (e : Expr) : EventsBounded (evaluate e).events (e.budget + 3) := by
  induction e with
  | literal q =>
    change EventsBounded ([event .dispatch [0]] ++ readCode q ++ writeCode q) (q.bits+1+3)
    apply events_append.mpr
    constructor
    · apply events_append.mpr
      exact ⟨dispatch_bounded 0 (by omega) _,
        read_bounded (Code.bounded_mono q.bounded_of_bits (by omega))⟩
    · exact write_bounded (Code.bounded_mono q.bounded_of_bits (by omega))
  | add a b ha hb =>
    have left := events_mono ha (show a.budget+3 ≤ (Expr.add a b).budget+3 by simp [Expr.budget]; omega)
    have right := events_mono hb (show b.budget+3 ≤ (Expr.add a b).budget+3 by simp [Expr.budget]; omega)
    have operation := events_mono (add_bounded a.evaluate_bounded b.evaluate_bounded)
      (show a.budget+b.budget+3 ≤ (Expr.add a b).budget+3 by simp [Expr.budget])
    simp only [evaluate, evaluate_value]
    apply events_append.mpr
    refine ⟨events_append.mpr ⟨events_append.mpr ⟨events_append.mpr ⟨?_, left⟩, right⟩, operation⟩, ?_⟩
    · exact dispatch_bounded 1 (by omega) _
    · exact write_bounded (Code.bounded_mono (Expr.add a b).evaluate_bounded (by omega))
  | mul a b ha hb =>
    have left := events_mono ha (show a.budget+3 ≤ (Expr.mul a b).budget+3 by simp [Expr.budget])
    have right := events_mono hb (show b.budget+3 ≤ (Expr.mul a b).budget+3 by simp [Expr.budget])
    have operation := mul_bounded a.evaluate_bounded b.evaluate_bounded
    simp only [evaluate, evaluate_value]
    apply events_append.mpr
    refine ⟨events_append.mpr ⟨events_append.mpr ⟨events_append.mpr ⟨?_, left⟩, right⟩, operation⟩, ?_⟩
    · exact dispatch_bounded 2 (by omega) _
    · exact write_bounded (Code.bounded_mono (Expr.mul a b).evaluate_bounded (by omega))
  | neg a ha =>
    simp only [evaluate, evaluate_value]
    apply events_append.mpr
    refine ⟨events_append.mpr ⟨events_append.mpr ⟨?_, ha⟩, neg_bounded a.evaluate_bounded⟩, ?_⟩
    · exact dispatch_bounded 3 (by omega) _
    · exact write_bounded (Code.bounded_mono (Expr.neg a).evaluate_bounded (by omega))
  | inv a ha =>
    simp only [evaluate, evaluate_value]
    apply events_append.mpr
    refine ⟨events_append.mpr ⟨events_append.mpr ⟨?_, ha⟩, inv_bounded a.evaluate_bounded⟩, ?_⟩
    · exact dispatch_bounded 4 (by omega) _
    · rw [inv_value]
      exact write_bounded (Code.bounded_mono (Expr.inv a).evaluate_bounded (by omega))

theorem evaluate_word_bits (e : Expr) (L : ℕ) (positive : 0 < L)
    (leaves : e.maxLeafBudget ≤ L) (entry : Event) (member : entry ∈ (evaluate e).events)
    (z : ℤ) (operand : z ∈ entry.values) : z.natAbs.size + 1 ≤ e.treeSize * L + 4 := by
  have magnitude := Nat.size_le.mpr (evaluate_bounded e entry member z operand)
  have budget := e.budget_le_size_mul L positive leaves
  omega

/-- Signed-denominator comparison, tracing all three integer crossproducts. -/
def lessEqual (q r : Code) : Result Bool :=
  let denominator := q.denominator * r.denominator
  let positive := 0 < denominator
  let left := q.numerator * r.denominator
  let right := r.numerator * q.denominator
  let result := if positive then decide (left ≤ right) else decide (right ≤ left)
  ⟨result, readCode q ++ readCode r ++
    [event .mul [q.denominator, r.denominator, denominator],
     event .less [0, denominator], event .branch [if positive then 1 else 0],
     event .mul [q.numerator, r.denominator, left],
     event .mul [r.numerator, q.denominator, right],
     event .le (if positive then [left, right] else [right, left]),
     event .write [if result then 1 else 0]]⟩

@[simp] theorem lessEqual_value (q r : Code) : (lessEqual q r).value = q.lessEqual r := rfl
@[simp] theorem lessEqual_length (q r : Code) : (lessEqual q r).events.length = 9 := rfl

theorem lessEqual_bounded {q r : Code} {k l : ℕ} (hq : q.Bounded k) (hr : r.Bounded l) :
    EventsBounded (lessEqual q r).events (k+l+3) := by
  have qb := Code.bounded_mono hq (show k ≤ k+l+3 by omega)
  have rb := Code.bounded_mono hr (show l ≤ k+l+3 by omega)
  have prod1 := (product_bound hq.1 hr.2).trans_le
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show k+l ≤ k+l+3 by omega))
  have prod2 := (product_bound hr.1 hq.2).trans_le
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show l+k ≤ k+l+3 by omega))
  have prod3 := (product_bound hq.2 hr.2).trans_le
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show k+l ≤ k+l+3 by omega))
  have zero : (0 : ℕ) < 2^(k+l+3) := by positivity
  have one : (1 : ℕ) < 2^(k+l+3) := Nat.one_lt_pow (by omega) (by decide)
  by_cases positive : 0 < q.denominator * r.denominator <;>
    by_cases first : q.numerator * r.denominator ≤ r.numerator * q.denominator <;>
    by_cases second : r.numerator * q.denominator ≤ q.numerator * r.denominator <;>
    simp [EventsBounded, lessEqual, readCode, event, positive, first, second,
      qb.1, qb.2, rb.1, rb.2, prod1, prod2, prod3, zero, one]

def EventsWidth (events : List Event) (width : ℕ) : Prop :=
  ∀ entry ∈ events, entry.values.length ≤ width

private theorem width_append {a b : List Event} {width : ℕ} :
    EventsWidth (a ++ b) width ↔ EventsWidth a width ∧ EventsWidth b width := by
  constructor
  · intro bound
    exact ⟨fun entry member => bound entry (List.mem_append_left _ member),
      fun entry member => bound entry (List.mem_append_right _ member)⟩
  · rintro ⟨left, right⟩ entry member
    rcases List.mem_append.mp member with member | member
    · exact left entry member
    · exact right entry member

private theorem width_add (q r : Code) : EventsWidth (add q r).events 3 := by
  simp [EventsWidth, add, readCode, event]
private theorem width_mul (q r : Code) : EventsWidth (mul q r).events 3 := by
  simp [EventsWidth, mul, readCode, event]
private theorem width_neg (q : Code) : EventsWidth (neg q).events 3 := by
  simp [EventsWidth, neg, readCode, event]
private theorem width_inv (q : Code) : EventsWidth (inv q).events 3 := by
  unfold inv
  split_ifs <;> simp [EventsWidth, readCode, event]
theorem lessEqual_width (q r : Code) : EventsWidth (lessEqual q r).events 3 := by
  by_cases positive : 0 < q.denominator*r.denominator <;>
    simp [EventsWidth, lessEqual, readCode, event, positive]

private theorem width_write (q : Code) : EventsWidth (writeCode q) 3 := by
  simp [EventsWidth, writeCode, event]
private theorem width_read (q : Code) : EventsWidth (readCode q) 3 := by
  simp [EventsWidth, readCode, event]
private theorem width_dispatch (tag : ℤ) : EventsWidth [event .dispatch [tag]] 3 := by
  simp [EventsWidth, event]

theorem evaluate_width (e : Expr) : EventsWidth (evaluate e).events 3 := by
  induction e with
  | literal q => exact width_append.mpr ⟨width_append.mpr ⟨width_dispatch _, width_read _⟩, width_write _⟩
  | add a b ha hb =>
    exact width_append.mpr ⟨width_append.mpr ⟨width_append.mpr ⟨width_append.mpr
      ⟨width_dispatch _, ha⟩, hb⟩, width_add _ _⟩, width_write _⟩
  | mul a b ha hb =>
    exact width_append.mpr ⟨width_append.mpr ⟨width_append.mpr ⟨width_append.mpr
      ⟨width_dispatch _, ha⟩, hb⟩, width_mul _ _⟩, width_write _⟩
  | neg a ha =>
    exact width_append.mpr ⟨width_append.mpr ⟨width_append.mpr
      ⟨width_dispatch _, ha⟩, width_neg _⟩, width_write _⟩
  | inv a ha =>
    exact width_append.mpr ⟨width_append.mpr ⟨width_append.mpr
      ⟨width_dispatch _, ha⟩, width_inv _⟩, width_write _⟩

/-- A closed quadratic word-charge for these read/write, sign, comparison,
addition and multiplication primitives. It bounds an arithmetic schedule;
no claim about Lean's compiled machine code is made. -/
def bitWork (events : List Event) : ℕ :=
  (events.map fun entry => ((entry.values.map fun z => z.natAbs.size+1).sum+1)^2).sum

private theorem sum_const {A : Type} (items : List A) (n : ℕ) :
    (items.map fun _ => n).sum = items.length*n := by
  induction items <;> simp_all [Nat.add_mul, Nat.add_comm]

theorem bitWork_bound (events : List Event) (width budget : ℕ)
    (count : EventsWidth events width)
    (words : ∀ entry ∈ events, ∀ z ∈ entry.values, z.natAbs.size+1 ≤ budget) :
    bitWork events ≤ events.length*(width*budget+1)^2 := by
  have each : ∀ entry ∈ events,
      ((entry.values.map fun z => z.natAbs.size+1).sum+1)^2 ≤ (width*budget+1)^2 := by
    intro entry member
    have sum : (entry.values.map fun z => z.natAbs.size+1).sum ≤ entry.values.length*budget := by
      rw [← sum_const entry.values budget]
      exact List.sum_le_sum (words entry member)
    have total : (entry.values.map fun z => z.natAbs.size+1).sum+1 ≤ width*budget+1 := by
      exact Nat.add_le_add_right (sum.trans (Nat.mul_le_mul_right budget (count entry member))) 1
    exact Nat.pow_le_pow_left total 2
  unfold bitWork
  rw [← sum_const events ((width*budget+1)^2)]
  exact List.sum_le_sum each

/-- Polynomial arithmetic count and signed-word charge for the actual raw
helper expression evaluator, including intermediate crossproducts. -/
theorem evaluation_contract (e : Expr) (L : ℕ) (positive : 0 < L)
    (leaves : e.maxLeafBudget ≤ L) :
    (evaluate e).value = e.evaluate.1 ∧
    (evaluate e).events.length ≤ 10*e.treeSize ∧
    bitWork (evaluate e).events ≤
      (10*e.treeSize)*(3*(e.treeSize*L+4)+1)^2 := by
  refine ⟨evaluate_value e, evaluate_length e, ?_⟩
  exact (bitWork_bound _ 3 _ (evaluate_width e)
    (evaluate_word_bits e L positive leaves)).trans
      (Nat.mul_le_mul_right _ (evaluate_length e))

end BuyAtBulk.Computation.Runtime.RawExpression
