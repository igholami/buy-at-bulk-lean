import BuyAtBulk.Computation.Rational.Encoding

/-! Bit bounds for expanded rational expression trees. Repeated occurrences
of a shared value count repeatedly: no bound for a shared arithmetic circuit
is inferred from its number of distinct nodes. -/
namespace BuyAtBulk.Computation.Rational

inductive Expr where
  | literal : Code → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | neg : Expr → Expr
  | inv : Expr → Expr

namespace Expr

def value : Expr → ℚ
  | .literal q => q.value
  | .add a b => a.value + b.value
  | .mul a b => a.value * b.value
  | .neg a => -a.value
  | .inv a => a.value⁻¹

def evaluate : Expr → Code × ℕ
  | .literal q => (q, 1)
  | .add a b =>
      let qa := a.evaluate
      let qb := b.evaluate
      (qa.1.add qb.1, qa.2 + qb.2 + 1)
  | .mul a b =>
      let qa := a.evaluate
      let qb := b.evaluate
      (qa.1.mul qb.1, qa.2 + qb.2 + 1)
  | .neg a => let qa := a.evaluate; (qa.1.neg, qa.2 + 1)
  | .inv a => let qa := a.evaluate; (qa.1.inv, qa.2 + 1)

def treeSize : Expr → ℕ
  | .literal _ => 1
  | .add a b | .mul a b => a.treeSize + b.treeSize + 1
  | .neg a | .inv a => a.treeSize + 1

/-- An exponent bounding both unreduced integer components. -/
def budget : Expr → ℕ
  | .literal q => q.bits + 1
  | .add a b => a.budget + b.budget + 1
  | .mul a b => a.budget + b.budget
  | .neg a | .inv a => a.budget

def maxLeafBudget : Expr → ℕ
  | .literal q => q.bits + 1
  | .add a b | .mul a b => max a.maxLeafBudget b.maxLeafBudget
  | .neg a | .inv a => a.maxLeafBudget

@[simp] theorem evaluate_value (expression : Expr) : expression.evaluate.1.value = expression.value := by
  induction expression with
  | literal q => rfl
  | add a b ha hb => simpa only [evaluate, value, Code.add_value] using congrArg₂ (· + ·) ha hb
  | mul a b ha hb => simpa only [evaluate, value, Code.mul_value] using congrArg₂ (· * ·) ha hb
  | neg a ha => simpa only [evaluate, value, Code.neg_value] using congrArg Neg.neg ha
  | inv a ha => simpa only [evaluate, value, Code.inv_value] using congrArg Inv.inv ha

@[simp] theorem evaluate_count (expression : Expr) : expression.evaluate.2 = expression.treeSize := by
  induction expression <;> simp_all [evaluate, treeSize]

theorem budget_pos (expression : Expr) : 0 < expression.budget := by
  induction expression <;> simp_all [budget] <;> omega

theorem maxLeafBudget_pos (expression : Expr) : 0 < expression.maxLeafBudget := by
  induction expression <;> simp_all [maxLeafBudget] <;> omega

theorem evaluate_bounded (expression : Expr) : expression.evaluate.1.Bounded expression.budget := by
  induction expression with
  | literal q => exact q.bounded_of_bits
  | add a b ha hb => exact Code.add_bounded ha hb
  | mul a b ha hb => exact Code.mul_bounded ha hb
  | neg a ha => exact Code.neg_bounded ha
  | inv a ha => exact Code.inv_bounded ha a.budget_pos

theorem budget_le_size_mul (expression : Expr) (L : ℕ) (positive : 0 < L)
    (leaves : expression.maxLeafBudget ≤ L) : expression.budget ≤ expression.treeSize * L := by
  induction expression with
  | literal q => simpa [budget, treeSize, maxLeafBudget] using leaves
  | add a b ha hb =>
    have left := ha (le_trans (le_max_left ..) leaves)
    have right := hb (le_trans (le_max_right ..) leaves)
    dsimp [budget, treeSize]
    nlinarith
  | mul a b ha hb =>
    have left := ha (le_trans (le_max_left ..) leaves)
    have right := hb (le_trans (le_max_right ..) leaves)
    dsimp [budget, treeSize]
    nlinarith
  | neg a ha =>
    have smaller := ha leaves
    dsimp [budget, treeSize]
    nlinarith
  | inv a ha =>
    have smaller := ha leaves
    dsimp [budget, treeSize]
    nlinarith

/-- Actual intermediate integer pairs, in postorder evaluation order. -/
def trace : Expr → List Code
  | .literal q => [q]
  | .add a b => a.trace ++ b.trace ++ [(Expr.add a b).evaluate.1]
  | .mul a b => a.trace ++ b.trace ++ [(Expr.mul a b).evaluate.1]
  | .neg a => a.trace ++ [(Expr.neg a).evaluate.1]
  | .inv a => a.trace ++ [(Expr.inv a).evaluate.1]

/-- Concrete evaluation has linear arithmetic work in the expanded tree,
and output representation length linear in tree size times input bit budget. -/
theorem evaluation_contract (expression : Expr) (L : ℕ) (positive : 0 < L)
    (leaves : expression.maxLeafBudget ≤ L) :
    expression.evaluate.1.value = expression.value ∧
    expression.evaluate.2 = expression.treeSize ∧
    expression.evaluate.1.bits ≤ 2 * expression.treeSize * L + 2 := by
  refine ⟨expression.evaluate_value, expression.evaluate_count, ?_⟩
  have encoded := Code.bounded_bits expression.evaluate_bounded
  have budget := expression.budget_le_size_mul L positive leaves
  nlinarith

theorem trace_bounded (expression : Expr) :
    ∀ q ∈ expression.trace, q.Bounded expression.budget := by
  induction expression with
  | literal q =>
    intro p member
    have : p = q := by simpa [trace] using member
    subst p
    exact q.bounded_of_bits
  | add a b ha hb =>
    intro q member
    simp only [trace, List.mem_append, List.mem_singleton] at member
    rcases member with (member | member) | rfl
    · exact Code.bounded_mono (ha q member) (by dsimp [budget]; omega)
    · exact Code.bounded_mono (hb q member) (by dsimp [budget]; omega)
    · exact (Expr.add a b).evaluate_bounded
  | mul a b ha hb =>
    intro q member
    simp only [trace, List.mem_append, List.mem_singleton] at member
    rcases member with (member | member) | rfl
    · exact Code.bounded_mono (ha q member) (by dsimp [budget]; omega)
    · exact Code.bounded_mono (hb q member) (by dsimp [budget]; omega)
    · exact (Expr.mul a b).evaluate_bounded
  | neg a ha =>
    intro q member
    simp only [trace, List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact ha q member
    · exact (Expr.neg a).evaluate_bounded
  | inv a ha =>
    intro q member
    simp only [trace, List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact ha q member
    · exact (Expr.inv a).evaluate_bounded

theorem intermediate_bits (expression : Expr) (L : ℕ) (positive : 0 < L)
    (leaves : expression.maxLeafBudget ≤ L) (q : Code) (member : q ∈ expression.trace) :
    q.bits ≤ 2 * expression.treeSize * L + 2 := by
  have encoded := Code.bounded_bits (expression.trace_bounded q member)
  have budget := expression.budget_le_size_mul L positive leaves
  nlinarith

/-- The same bound holds for the normalized rational used by metric and
LP interfaces, without assuming normalization preserves the unreduced pair. -/
theorem normalized_bits (expression : Expr) (L : ℕ) (positive : 0 < L)
    (leaves : expression.maxLeafBudget ≤ L) :
    (Code.ofRat expression.value).bits ≤ 2 * expression.treeSize * L + 2 := by
  rw [← expression.evaluate_value]
  exact (Code.normalized_bits_le expression.evaluate.1).trans
    (expression.evaluation_contract L positive leaves).2.2

end Expr
end BuyAtBulk.Computation.Rational
