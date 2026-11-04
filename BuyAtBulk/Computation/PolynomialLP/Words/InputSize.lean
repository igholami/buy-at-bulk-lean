import BuyAtBulk.Computation.PolynomialLP.QueryBounds
import BuyAtBulk.Computation.PolynomialLP.BudgetTrace
import BuyAtBulk.Computation.PolynomialLP.BoxTrace

/-! Stored-cell encodings and total input length have explicit polynomial
relations. Adding the unit box preserves a uniform normalized scalar bound. -/
namespace BuyAtBulk.PolynomialLP
open Computation.Rational
variable {n m : ℕ}

theorem CellBits.mono {input : Stored (n := n) (m := m)} {A B : ℕ}
    (cells : CellBits input A) (bound : A ≤ B) : CellBits input B :=
  ⟨fun i j => (cells.coefficients i j).trans bound,
    fun i => (cells.bounds i).trans bound, fun j => (cells.objective j).trans bound⟩

theorem input_cellBits (input : Stored (n := n) (m := m)) : CellBits input (2 * inputBudget input + 2) := by
  constructor
  · intro i j
    exact Code.bounded_bits (inputBudget_coefficient input i j)
  · intro i
    exact Code.bounded_bits (inputBudget_bound input i)
  · intro j
    have bound := InputTrace.inputBudget_objective_bits input j
    omega

theorem CellBits.inputBudget {input : Stored (n := n) (m := m)} {L : ℕ}
    (cells : CellBits input L) : inputBudget input ≤ 1 + (m + m * n + n) * L := by
  have bounds := InputTrace.vectorBudget_bound input.bounds L cells.bounds
  have coefficients := InputTrace.matrixBudgetScan_bound input.coefficients (List.finRange m) L (fun i _ => cells.coefficients i)
  have objective := InputTrace.vectorBudget_bound input.objective L cells.objective
  simp only [List.length_finRange] at coefficients
  rw [← InputTrace.inputBudgetTrace_value]
  simp only [InputTrace.inputBudgetTrace, Computation.Runtime.Traced.bind_value,
    Computation.Runtime.emit_value, Computation.Runtime.indexList_value]
  nlinarith

theorem CellBits.boxed {input : Stored (n := n) (m := m)} {L : ℕ}
    (cells : CellBits input L) : CellBits input.boxed (L + 4) := by
  constructor
  · intro i
    apply Fin.addCases (motive := fun i => ∀ j : Fin n,
      (Code.ofRat input.boxed.coefficients[i.val][j.val]).bits ≤ L + 4) _ _ i
    · intro i j
      simpa [Stored.boxed, Stored.extend] using (cells.coefficients i j).trans (Nat.le_add_right L 4)
    · intro k
      apply Fin.addCases (motive := fun k => ∀ j : Fin n,
        (Code.ofRat input.boxed.coefficients[(Fin.natAdd m k).val][j.val]).bits ≤ L + 4) _ _ k
      · intro i j
        by_cases same : i = j <;> simp [Stored.boxed, Stored.extend, coordinateRows, same, Code.bits, Code.ofRat] <;> omega
      · intro i j
        by_cases same : i = j <;> simp [Stored.boxed, Stored.extend, coordinateRows, same, Code.bits, Code.ofRat] <;> omega
  · intro i
    apply Fin.addCases (motive := fun i => (Code.ofRat input.boxed.bounds[i.val]).bits ≤ L + 4) _ _ i
    · intro i
      simpa [Stored.boxed, Stored.extend] using (cells.bounds i).trans (Nat.le_add_right L 4)
    · intro k
      apply Fin.addCases (motive := fun k => (Code.ofRat input.boxed.bounds[(Fin.natAdd m k).val]).bits ≤ L + 4) _ _ k
      · intro i
        simp [Stored.boxed, Stored.extend, Code.bits, Code.ofRat]
      · intro i
        simp [Stored.boxed, Stored.extend, Code.bits, Code.ofRat]
  · intro j
    exact (cells.objective j).trans (Nat.le_add_right L 4)

end BuyAtBulk.PolynomialLP
