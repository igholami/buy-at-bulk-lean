import BuyAtBulk.Computation.Rational.Expression
import BuyAtBulk.UpperBound.ConditionalExpectation

/-! Expanded rational expression trees for the helper's actual pessimistic
estimator. Products and sums are expanded over explicit node/row lists. Their
size is polynomial, so expression bit bounds apply to every intermediate. -/
namespace BuyAtBulk.Computation.HelperExpressions
open Rational

def atom (q : ℚ) : Expr := .literal (Code.ofRat q)
def sum : List Expr → Expr
  | [] => atom 0
  | a :: rest => .add a (sum rest)
def product : List Expr → Expr
  | [] => atom 1
  | a :: rest => .mul a (product rest)

@[simp] theorem atom_value (q : ℚ) : (atom q).value = q := by simp [atom, Expr.value]
@[simp] theorem atom_size (q : ℚ) : (atom q).treeSize = 1 := rfl

@[simp] theorem sum_value (expressions : List Expr) :
    (sum expressions).value = (expressions.map Expr.value).sum := by
  induction expressions <;> simp_all [sum, Expr.value]

@[simp] theorem product_value (expressions : List Expr) :
    (product expressions).value = (expressions.map Expr.value).prod := by
  induction expressions <;> simp_all [product, Expr.value]

@[simp] theorem sum_size (expressions : List Expr) :
    (sum expressions).treeSize = (expressions.map Expr.treeSize).sum + expressions.length + 1 := by
  induction expressions <;> simp_all [sum, Expr.treeSize] <;> omega

@[simp] theorem product_size (expressions : List Expr) :
    (product expressions).treeSize = (expressions.map Expr.treeSize).sum + expressions.length + 1 := by
  induction expressions <;> simp_all [product, Expr.treeSize] <;> omega

private theorem map_const_sum {A : Type} (items : List A) (n : ℕ) :
    (items.map fun _ => n).sum = items.length * n := by
  induction items <;> simp_all [Nat.add_mul, Nat.add_comm]

theorem sum_leaf_bound (expressions : List Expr) (L : ℕ)
    (constant : (atom 0).maxLeafBudget ≤ L)
    (each : ∀ e ∈ expressions, e.maxLeafBudget ≤ L) : (sum expressions).maxLeafBudget ≤ L := by
  induction expressions with
  | nil => exact constant
  | cons a rest ih =>
    exact max_le (each a (by simp)) (ih (fun e member => each e (by simp [member])))

theorem product_leaf_bound (expressions : List Expr) (L : ℕ)
    (constant : (atom 1).maxLeafBudget ≤ L)
    (each : ∀ e ∈ expressions, e.maxLeafBudget ≤ L) : (product expressions).maxLeafBudget ≤ L := by
  induction expressions with
  | nil => exact constant
  | cons a rest ih =>
    exact max_le (each a (by simp)) (ih (fun e member => each e (by simp [member])))

/-- Normalized sums have polynomial binary length in an explicit coefficient
list, including zero terms and negative coefficients. -/
theorem sum_rat_bits (terms : List ℚ) (L : ℕ) (constant : 5 ≤ L)
    (inputs : ∀ q ∈ terms, (Code.ofRat q).bits + 1 ≤ L) :
    (Code.ofRat terms.sum).bits ≤ 2 * (2 * terms.length + 1) * L + 2 := by
  let expression := sum (terms.map atom)
  have leaves : expression.maxLeafBudget ≤ L := by
    apply sum_leaf_bound _ _ (by exact (by decide : (atom 0).maxLeafBudget ≤ 5).trans constant)
    intro e member
    obtain ⟨q, q_member, same⟩ := List.mem_map.mp member
    subst e
    exact inputs q q_member
  have decoded : expression.value = terms.sum := by simp [expression, List.map_map, Function.comp_def]
  have size : expression.treeSize = 2 * terms.length + 1 := by
    simp [expression, List.map_map, Function.comp_def]
    <;> ring
  have bound := expression.normalized_bits L (by omega) leaves
  simpa only [decoded, size] using bound

/-- Compact LP budgets and per-commodity physical costs are sums of products.
Their binary lengths are controlled by the stored rational input entries. -/
theorem sum_products_bits (terms : List (ℚ × ℚ)) (L : ℕ) (constant : 5 ≤ L)
    (inputs : ∀ q ∈ terms, (Code.ofRat q.1).bits + 1 ≤ L ∧ (Code.ofRat q.2).bits + 1 ≤ L) :
    (Code.ofRat (terms.map fun q => q.1 * q.2).sum).bits ≤
      2 * (4 * terms.length + 1) * L + 2 := by
  let expression := sum (terms.map fun q => Expr.mul (atom q.1) (atom q.2))
  have leaves : expression.maxLeafBudget ≤ L := by
    apply sum_leaf_bound _ _ (by exact (by decide : (atom 0).maxLeafBudget ≤ 5).trans constant)
    intro e member
    obtain ⟨q, q_member, same⟩ := List.mem_map.mp member
    subst e
    exact max_le (inputs q q_member).1 (inputs q q_member).2
  have decoded : expression.value = (terms.map fun q => q.1 * q.2).sum := by
    simp [expression, Expr.value, List.map_map, Function.comp_def]
  have size : expression.treeSize = 4 * terms.length + 1 := by
    simp [expression, Expr.treeSize, List.map_map, Function.comp_def]
    <;> ring
  have bound := expression.normalized_bits L (by omega) leaves
  simpa only [decoded, size] using bound

variable {V R : Type}

def remainingFactor (probability factor : ℚ) : Expr :=
  .add (.add (atom 1) (.neg (atom probability))) (.mul (atom probability) (atom factor))

def row (probability : V → ℚ) (factor : V → ℚ) (amplitude : ℚ)
    (selected remaining : List V) : Expr :=
  .mul (.mul (atom amplitude) (product (selected.map fun v => atom (factor v))))
    (product (remaining.map fun v => remainingFactor (probability v) (factor v)))

def potential (buying probability : V → ℚ) (factor : R → V → ℚ)
    (amplitude : R → ℚ) (fixedCost normalization : ℚ) (rows : List R)
    (selected remaining : List V) : Expr :=
  .add (.mul (.add (.add (atom fixedCost) (sum (selected.map fun v => atom (buying v))))
      (sum (remaining.map fun v => .mul (atom (probability v)) (atom (buying v)))))
      (.inv (atom normalization)))
    (sum (rows.map fun r => row probability (factor r) (amplitude r) selected remaining))

@[simp] theorem remainingFactor_size (p f : ℚ) : (remainingFactor p f).treeSize = 8 := rfl

@[simp] theorem row_size (probability factor : V → ℚ) (amplitude : ℚ)
    (selected remaining : List V) :
    (row probability factor amplitude selected remaining).treeSize =
      2 * selected.length + 9 * remaining.length + 5 := by
  simp [row, Expr.treeSize, List.map_map, Function.comp_def, map_const_sum]
  <;> ring

theorem potential_size (buying probability : V → ℚ) (factor : R → V → ℚ)
    (amplitude : R → ℚ) (fixedCost normalization : ℚ) (rows : List R)
    (selected remaining : List V) :
    (potential buying probability factor amplitude fixedCost normalization rows selected remaining).treeSize =
      2 * selected.length + 4 * remaining.length + 10 +
        rows.length * (2 * selected.length + 9 * remaining.length + 6) := by
  simp [potential, Expr.treeSize, List.map_map, Function.comp_def, map_const_sum]
  <;> ring

theorem potential_size_bound (buying probability : V → ℚ) (factor : R → V → ℚ)
    (amplitude : R → ℚ) (fixedCost normalization : ℚ) (rows : List R)
    (selected remaining : List V) :
    (potential buying probability factor amplitude fixedCost normalization rows selected remaining).treeSize ≤
      12 * (rows.length + 1) * (selected.length + remaining.length + 1) := by
  rw [potential_size]
  nlinarith only [Nat.zero_le (rows.length * selected.length),
    Nat.zero_le (rows.length * remaining.length), Nat.zero_le selected.length,
    Nat.zero_le remaining.length, Nat.zero_le rows.length]

theorem potential_value (buying probability : V → ℚ) (factor : R → V → ℚ)
    (amplitude : R → ℚ) (fixedCost normalization : ℚ) (rows : List R)
    (selected remaining : List V) :
    (potential buying probability factor amplitude fixedCost normalization rows selected remaining).value =
      (fixedCost + (selected.map buying).sum + (remaining.map fun v => probability v * buying v).sum) / normalization +
      (rows.map fun r => amplitude r * (selected.map (factor r)).prod *
        (remaining.map fun v => 1 - probability v + probability v * factor r v).prod).sum := by
  simp [potential, row, remainingFactor, Expr.value, List.map_map, Function.comp_def, div_eq_mul_inv, sub_eq_add_neg]

/-- A concrete potential evaluation has polynomial expression work and
polynomial intermediate encoding length in the *factor* input bit budget L. -/
theorem potential_evaluation (buying probability : V → ℚ) (factor : R → V → ℚ)
    (amplitude : R → ℚ) (fixedCost normalization : ℚ) (rows : List R)
    (selected remaining : List V) (L : ℕ) (positive : 0 < L)
    (leaves : (potential buying probability factor amplitude fixedCost normalization rows selected remaining).maxLeafBudget ≤ L) :
    let expression := potential buying probability factor amplitude fixedCost normalization rows selected remaining
    expression.evaluate.1.value = expression.value ∧
      expression.evaluate.2 ≤ 12 * (rows.length + 1) * (selected.length + remaining.length + 1) ∧
      ∀ q ∈ expression.trace,
        q.bits ≤ 24 * (rows.length + 1) * (selected.length + remaining.length + 1) * L + 2 := by
  dsimp only
  let expression := potential buying probability factor amplitude fixedCost normalization rows selected remaining
  have size := potential_size_bound buying probability factor amplitude fixedCost normalization rows selected remaining
  refine ⟨expression.evaluate_value, ?_, ?_⟩
  · simpa only [Expr.evaluate_count] using size
  · intro q member
    have bound := expression.intermediate_bits L positive leaves q member
    dsimp [expression] at bound
    nlinarith [mul_le_mul_of_nonneg_right size (Nat.zero_le L)]

end BuyAtBulk.Computation.HelperExpressions
