import BuyAtBulk.Computation.PolynomialLP.StepRuntimeInvariant

/-! Polynomial encoding bounds for the materialized dot products in an
ellipsoid update. Bounds depend on binary leaf lengths and dimension. -/
namespace BuyAtBulk.PolynomialLP
open Computation.Rational
variable {n : ℕ}

def matrixProductBudget (n L : ℕ) : ℕ := 2 * (4 * n + 1) * L + 2

theorem matrixVector_bits (shape : Vector (Vector ℚ n) n) (direction : Vector ℚ n)
    (L : ℕ) (constant : 5 ≤ L)
    (shapeBits : ∀ i j : Fin n, (Code.ofRat shape[i.val][j.val]).bits + 1 ≤ L)
    (directionBits : ∀ j : Fin n, (Code.ofRat direction[j.val]).bits + 1 ≤ L)
    (i : Fin n) :
    (Code.ofRat (matrixVector shape direction)[i.val]).bits ≤ matrixProductBudget n L := by
  have bound := dot_output_bits shape[i.val] direction L constant (shapeBits i) directionBits
  simpa only [dot, dotScan_value, matrixVector, Vector.getElem_ofFn, matrixProductBudget] using bound

theorem quadratic_bits (shape : Vector (Vector ℚ n) n) (direction : Vector ℚ n)
    (L : ℕ) (constant : 5 ≤ L)
    (shapeBits : ∀ i j : Fin n, (Code.ofRat shape[i.val][j.val]).bits + 1 ≤ L)
    (directionBits : ∀ j : Fin n, (Code.ofRat direction[j.val]).bits + 1 ≤ L) :
    (Code.ofRat (quadratic shape direction)).bits ≤
      matrixProductBudget n (matrixProductBudget n L + L + 5) := by
  have bound := dot_output_bits direction (matrixVector shape direction)
    (matrixProductBudget n L + L + 5) (by omega)
    (fun j => (directionBits j).trans (by omega))
    (fun j => by have bit := matrixVector_bits shape direction L constant shapeBits directionBits j; omega)
  simpa only [dot, dotScan_value, quadratic, matrixProductBudget] using bound

theorem normalizationPrecision_bound (n : ℕ) : normalizationPrecision n ≤ 2 * n + 9 := by
  apply Nat.clog_le_of_le_pow
  have product := Nat.mul_le_mul (Nat.lt_two_pow_self (n := n)).le
    (Nat.lt_two_pow_self (n := n + 1)).le
  have scaled := Nat.mul_le_mul_left 256 product
  have powers : 256 * (2 ^ n * 2 ^ (n + 1)) = 2 ^ (2 * n + 9) := by
    rw [← pow_add, ← show (2 : ℕ) ^ 8 = 256 by norm_num, ← pow_add]
    congr 1
    omega
  simpa only [powers, Nat.mul_assoc] using scaled

def rootBudget (n Q : ℕ) : ℕ := 14 * Q + 8 * n + 80

theorem normalizationRoot_bits (q : ℚ) (n Q : ℕ) (input : (Code.ofRat q).bits ≤ Q) :
    (Code.ofRat (normalizationRoot q n)).bits ≤ rootBudget n Q := by
  have bound := (sqrtBracket_endpoint_bits q
    (3 * ((Code.ofRat q).bits + 1) + normalizationPrecision n + 3)
    ((Code.ofRat q).bits + 1) (Code.bounded_of_bits _)).2
  have precision := normalizationPrecision_bound n
  change (Code.ofRat (normalizationRoot q n)).bits ≤ _ at bound
  dsimp [rootBudget]
  omega

end BuyAtBulk.PolynomialLP
