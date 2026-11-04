import BuyAtBulk.Computation.Runtime.HelperEvaluation

/-! Actual expression construction from finite stored coefficient vectors.
Read events include row/vertex addresses and the rational's stored components.
Expression allocation is charged at each constructor. -/
namespace BuyAtBulk.Computation.Runtime.HelperConstruction
open Rational RawExpression
variable {n m : ℕ}

structure StoredTables (n m : ℕ) where
  buying : Vector ℚ n
  probability : Vector ℚ n
  factor : Vector (Vector ℚ n) m
  amplitude : Vector ℚ m
  fixedCost : ℚ
  normalization : ℚ
  rowOrder : List (Fin m)
  rowOrder_eq : rowOrder=List.finRange m

attribute [simp] StoredTables.rowOrder_eq

namespace StoredTables
def tables (stored : StoredTables n m) : HelperEvaluation.Tables (Fin n) (Fin m) where
  buying v := stored.buying[v.val]
  probability v := stored.probability[v.val]
  factor r v := stored.factor[r.val][v.val]
  amplitude r := stored.amplitude[r.val]
  fixedCost := stored.fixedCost
  normalization := stored.normalization
  rows := List.finRange m
end StoredTables

def literal (q : ℚ) : Result Expr :=
  ⟨HelperExpressions.atom q, [event .read [q.num,q.den], event .pair [0]]⟩

def readEntry {k : ℕ} (values : Vector ℚ k) (i : Fin k) : Result Expr :=
  let result := literal values[i.val]
  ⟨result.value, event .read [i.val] :: result.events⟩

def readFactor (values : Vector (Vector ℚ n) m) (r : Fin m) (v : Fin n) : Result Expr :=
  let result := readEntry values[r.val] v
  ⟨result.value, event .read [r.val] :: result.events⟩

def add (left right : Result Expr) : Result Expr :=
  ⟨Expr.add left.value right.value, left.events ++ right.events ++ [event .pair [1]]⟩
def mul (left right : Result Expr) : Result Expr :=
  ⟨Expr.mul left.value right.value, left.events ++ right.events ++ [event .pair [2]]⟩
def neg (child : Result Expr) : Result Expr :=
  ⟨Expr.neg child.value, child.events ++ [event .pair [3]]⟩
def inv (child : Result Expr) : Result Expr :=
  ⟨Expr.inv child.value, child.events ++ [event .pair [4]]⟩

def sum {A : Type} (build : A → Result Expr) : List A → Result Expr
  | [] => literal 0
  | a :: rest => add (build a) (sum build rest)
def product {A : Type} (build : A → Result Expr) : List A → Result Expr
  | [] => literal 1
  | a :: rest => mul (build a) (product build rest)

@[simp] theorem literal_value (q : ℚ) : (literal q).value = HelperExpressions.atom q := rfl
@[simp] theorem readEntry_value {k : ℕ} (values : Vector ℚ k) (i : Fin k) :
    (readEntry values i).value = HelperExpressions.atom values[i.val] := rfl
@[simp] theorem readFactor_value (values : Vector (Vector ℚ n) m) (r : Fin m) (v : Fin n) :
    (readFactor values r v).value = HelperExpressions.atom values[r.val][v.val] := rfl
@[simp] theorem add_value (a b : Result Expr) : (add a b).value = Expr.add a.value b.value := rfl
@[simp] theorem mul_value (a b : Result Expr) : (mul a b).value = Expr.mul a.value b.value := rfl
@[simp] theorem neg_value (a : Result Expr) : (neg a).value = Expr.neg a.value := rfl
@[simp] theorem inv_value (a : Result Expr) : (inv a).value = Expr.inv a.value := rfl
@[simp] theorem sum_value {A : Type} (build : A → Result Expr) (items : List A) :
    (sum build items).value = HelperExpressions.sum (items.map fun a => (build a).value) := by
  induction items <;> simp_all [sum, HelperExpressions.sum]
@[simp] theorem product_value {A : Type} (build : A → Result Expr) (items : List A) :
    (product build items).value = HelperExpressions.product (items.map fun a => (build a).value) := by
  induction items <;> simp_all [product, HelperExpressions.product]

def row (stored : StoredTables n m) (selected remaining : List (Fin n)) (r : Fin m) : Result Expr :=
  mul (mul (readEntry stored.amplitude r) (product (readFactor stored.factor r) selected))
    (product (fun v => add (add (literal 1) (neg (readEntry stored.probability v)))
      (mul (readEntry stored.probability v) (readFactor stored.factor r v))) remaining)

def potential (stored : StoredTables n m) (selected remaining : List (Fin n)) : Result Expr :=
  add (mul (add (add (literal stored.fixedCost) (sum (readEntry stored.buying) selected))
      (sum (fun v => mul (readEntry stored.probability v) (readEntry stored.buying v)) remaining))
      (inv (literal stored.normalization)))
    (sum (row stored selected remaining) stored.rowOrder)

theorem row_value (stored : StoredTables n m) (selected remaining : List (Fin n)) (r : Fin m) :
    (row stored selected remaining r).value = HelperExpressions.row stored.tables.probability
      (stored.tables.factor r) (stored.tables.amplitude r) selected remaining := by
  simp [row, HelperExpressions.row, HelperExpressions.remainingFactor, StoredTables.tables]

theorem potential_value (stored : StoredTables n m) (selected remaining : List (Fin n)) :
    (potential stored selected remaining).value = HelperEvaluation.potential stored.tables selected remaining := by
  simp [potential, HelperEvaluation.potential, HelperExpressions.potential, row_value, StoredTables.tables]

/-- Constructor and actual table-read cost, relative to the constructed syntax. -/
def CostBound (result : Result Expr) : Prop := result.events.length ≤ 4*result.value.treeSize

theorem literal_cost (q : ℚ) : CostBound (literal q) := by simp [CostBound, literal]
theorem readEntry_cost {k : ℕ} (values : Vector ℚ k) (i : Fin k) : CostBound (readEntry values i) := by
  simp [CostBound, readEntry, literal]
theorem readFactor_cost (values : Vector (Vector ℚ n) m) (r : Fin m) (v : Fin n) :
    CostBound (readFactor values r v) := by simp [CostBound, readFactor, readEntry, literal]

theorem add_cost {a b : Result Expr} (left : CostBound a) (right : CostBound b) : CostBound (add a b) := by
  simp only [CostBound, add, List.length_append, List.length_singleton, Expr.treeSize] at *
  omega

theorem mul_cost {a b : Result Expr} (left : CostBound a) (right : CostBound b) : CostBound (mul a b) := by
  simp only [CostBound, mul, List.length_append, List.length_singleton, Expr.treeSize] at *
  omega

theorem neg_cost {a : Result Expr} (child : CostBound a) : CostBound (neg a) := by
  simp only [CostBound, neg, List.length_append, List.length_singleton, Expr.treeSize] at *
  omega

theorem inv_cost {a : Result Expr} (child : CostBound a) : CostBound (inv a) := by
  simp only [CostBound, inv, List.length_append, List.length_singleton, Expr.treeSize] at *
  omega

theorem sum_cost {A : Type} (build : A → Result Expr) (items : List A)
    (each : ∀ a ∈ items, CostBound (build a)) : CostBound (sum build items) := by
  induction items with
  | nil => exact literal_cost 0
  | cons a rest ih =>
    exact add_cost (each a (by simp)) (ih (fun a member => each a (by simp [member])))

theorem product_cost {A : Type} (build : A → Result Expr) (items : List A)
    (each : ∀ a ∈ items, CostBound (build a)) : CostBound (product build items) := by
  induction items with
  | nil => exact literal_cost 1
  | cons a rest ih =>
    exact mul_cost (each a (by simp)) (ih (fun a member => each a (by simp [member])))

theorem row_cost (stored : StoredTables n m) (selected remaining : List (Fin n)) (r : Fin m) :
    CostBound (row stored selected remaining r) := by
  apply mul_cost
  · exact mul_cost (readEntry_cost _ _) (product_cost _ _ (fun v _ => readFactor_cost _ _ _))
  · apply product_cost
    intro v _
    exact add_cost (add_cost (literal_cost 1) (neg_cost (readEntry_cost _ _)))
      (mul_cost (readEntry_cost _ _) (readFactor_cost _ _ _))

theorem potential_cost (stored : StoredTables n m) (selected remaining : List (Fin n)) :
    CostBound (potential stored selected remaining) := by
  apply add_cost
  · apply mul_cost
    · apply add_cost
      · exact add_cost (literal_cost _) (sum_cost _ _ (fun v _ => readEntry_cost _ _))
      · exact sum_cost _ _ (fun v _ => mul_cost (readEntry_cost _ _) (readEntry_cost _ _))
    · exact inv_cost (literal_cost _)
  · exact sum_cost _ _ (fun r _ => row_cost stored selected remaining r)

theorem potential_polynomial (stored : StoredTables n m) (selected remaining : List (Fin n)) :
    (potential stored selected remaining).events.length ≤
      48*(m+1)*(selected.length+remaining.length+1) := by
  have cost := potential_cost stored selected remaining
  rw [CostBound, potential_value] at cost
  have size := HelperExpressions.potential_size_bound stored.tables.buying stored.tables.probability
    stored.tables.factor stored.tables.amplitude stored.tables.fixedCost stored.tables.normalization
    stored.tables.rows selected remaining
  have rows : stored.tables.rows.length = m := by simp [StoredTables.tables]
  change (HelperEvaluation.potential stored.tables selected remaining).treeSize ≤ _ at size
  rw [rows] at size
  nlinarith

theorem literal_bounded (q : ℚ) (K : ℕ) (bound : (Code.ofRat q).Bounded K) :
    EventsBounded (literal q).events K := by
  have zero : (0 : ℕ) < 2^K := by positivity
  have denominator : q.den < 2^K := by simpa only [Code.ofRat, Int.natAbs_natCast] using bound.2
  have numerator : q.num.natAbs < 2^K := bound.1
  simpa [EventsBounded, literal, event, zero, denominator] using numerator

private theorem index_bounded {k : ℕ} (v : Fin k) (K : ℕ) (index : k ≤ K) :
    (v.val : ℤ).natAbs < 2^K := by
  simp only [Int.natAbs_natCast]
  exact (v.isLt.trans Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_right (by decide) index)

theorem readEntry_bounded {k : ℕ} (values : Vector ℚ k) (v : Fin k) (K : ℕ)
    (indices : k ≤ K) (bound : (Code.ofRat values[v.val]).Bounded K) :
    EventsBounded (readEntry values v).events K := by
  change EventsBounded ([event .read [v.val]] ++ (literal values[v.val]).events) K
  apply events_append.mpr
  refine ⟨?_, literal_bounded _ _ bound⟩
  simpa [EventsBounded, event] using index_bounded v K indices

theorem readFactor_bounded (values : Vector (Vector ℚ n) m) (r : Fin m) (v : Fin n) (K : ℕ)
    (vertices : n ≤ K) (rows : m ≤ K) (bound : (Code.ofRat values[r.val][v.val]).Bounded K) :
    EventsBounded (readFactor values r v).events K := by
  change EventsBounded ([event .read [r.val]] ++ (readEntry values[r.val] v).events) K
  apply events_append.mpr
  refine ⟨?_, readEntry_bounded _ _ K vertices bound⟩
  simpa [EventsBounded, event] using index_bounded r K rows

private theorem tag_bounded (tag : ℕ) (K : ℕ) (small : tag ≤ 4) (large : 3 ≤ K) :
    EventsBounded [event .pair [(tag : ℤ)]] K := by
  have lower : (8 : ℕ) ≤ 2^K := by
    calc
      _ = 2^3 := by decide
      _ ≤ _ := Nat.pow_le_pow_right (by decide) large
  simp only [EventsBounded, List.mem_singleton, forall_eq, event, Int.natAbs_natCast]
  omega

theorem add_bounded {a b : Result Expr} {K : ℕ} (left : EventsBounded a.events K)
    (right : EventsBounded b.events K) (large : 3 ≤ K) : EventsBounded (add a b).events K :=
  events_append.mpr ⟨events_append.mpr ⟨left,right⟩,tag_bounded 1 K (by omega) large⟩
theorem mul_bounded {a b : Result Expr} {K : ℕ} (left : EventsBounded a.events K)
    (right : EventsBounded b.events K) (large : 3 ≤ K) : EventsBounded (mul a b).events K :=
  events_append.mpr ⟨events_append.mpr ⟨left,right⟩,tag_bounded 2 K (by omega) large⟩
theorem neg_bounded {a : Result Expr} {K : ℕ} (child : EventsBounded a.events K)
    (large : 3 ≤ K) : EventsBounded (neg a).events K :=
  events_append.mpr ⟨child,tag_bounded 3 K (by omega) large⟩
theorem inv_bounded {a : Result Expr} {K : ℕ} (child : EventsBounded a.events K)
    (large : 3 ≤ K) : EventsBounded (inv a).events K :=
  events_append.mpr ⟨child,tag_bounded 4 K (by omega) large⟩

private theorem zero_bounded (K : ℕ) (large : 5 ≤ K) : EventsBounded (literal 0).events K := by
  apply literal_bounded
  exact Code.bounded_mono (Code.ofRat 0).bounded_of_bits (by exact (by decide : (Code.ofRat 0).bits+1 ≤ 5).trans large)
private theorem one_bounded (K : ℕ) (large : 5 ≤ K) : EventsBounded (literal 1).events K := by
  apply literal_bounded
  exact Code.bounded_mono (Code.ofRat 1).bounded_of_bits (by exact (by decide : (Code.ofRat 1).bits+1 ≤ 5).trans large)

theorem sum_bounded {A : Type} (build : A → Result Expr) (items : List A) (K : ℕ)
    (large : 5 ≤ K) (each : ∀ a ∈ items, EventsBounded (build a).events K) :
    EventsBounded (sum build items).events K := by
  induction items with
  | nil => exact zero_bounded K large
  | cons a rest ih =>
    exact add_bounded (each a (by simp))
      (ih (fun a member => each a (by simp [member]))) (by omega)

theorem product_bounded {A : Type} (build : A → Result Expr) (items : List A) (K : ℕ)
    (large : 5 ≤ K) (each : ∀ a ∈ items, EventsBounded (build a).events K) :
    EventsBounded (product build items).events K := by
  induction items with
  | nil => exact one_bounded K large
  | cons a rest ih =>
    exact mul_bounded (each a (by simp))
      (ih (fun a member => each a (by simp [member]))) (by omega)

theorem potential_bounded (stored : StoredTables n m) (selected remaining : List (Fin n))
    (L : ℕ) (coefficients : HelperEvaluation.CoefficientsBounded stored.tables L) :
    EventsBounded (potential stored selected remaining).events (L+n+m+5) := by
  let K := L+n+m+5
  have large : 5 ≤ K := by dsimp [K]; omega
  have three : 3 ≤ K := by omega
  have vertices : n ≤ K := by dsimp [K]; omega
  have rows : m ≤ K := by dsimp [K]; omega
  have lift_bound (q : ℚ) (input : (Code.ofRat q).bits+1 ≤ L) : (Code.ofRat q).Bounded K :=
    Code.bounded_mono (Code.ofRat q).bounded_of_bits (by dsimp [K]; omega)
  have buying (v : Fin n) := readEntry_bounded stored.buying v K vertices (lift_bound _ (coefficients.buying v))
  have probability (v : Fin n) := readEntry_bounded stored.probability v K vertices (lift_bound _ (coefficients.probability v))
  have factor (r : Fin m) (v : Fin n) := readFactor_bounded stored.factor r v K vertices rows
    (lift_bound _ (coefficients.factor r (by simp [StoredTables.tables]) v))
  have amplitude (r : Fin m) := readEntry_bounded stored.amplitude r K rows
    (lift_bound _ (coefficients.amplitude r (by simp [StoredTables.tables])))
  have fixed := literal_bounded stored.fixedCost K (lift_bound _ coefficients.fixedCost)
  have normalization := literal_bounded stored.normalization K (lift_bound _ coefficients.normalization)
  have row_bound (r : Fin m) : EventsBounded (row stored selected remaining r).events K := by
    apply mul_bounded
    · exact mul_bounded (amplitude r) (product_bounded _ _ K large (fun v _ => factor r v)) three
    · apply product_bounded _ _ K large
      intro v _
      exact add_bounded (add_bounded (one_bounded K large) (neg_bounded (probability v) three) three)
        (mul_bounded (probability v) (factor r v) three) three
    · exact three
  apply add_bounded
  · apply mul_bounded
    · exact add_bounded (add_bounded fixed (sum_bounded _ _ K large (fun v _ => buying v)) three)
        (sum_bounded _ _ K large (fun v _ => mul_bounded (probability v) (buying v) three)) three
    · exact inv_bounded normalization three
    · exact three
  · exact sum_bounded _ _ K large (fun r _ => row_bound r)
  · exact three

end BuyAtBulk.Computation.Runtime.HelperConstruction
