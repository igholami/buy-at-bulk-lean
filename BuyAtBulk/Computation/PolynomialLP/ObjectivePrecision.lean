import BuyAtBulk.Computation.PolynomialLP.VertexEncoding
import BuyAtBulk.Computation.PolynomialLP.RationalGap
import BuyAtBulk.Computation.HelperExpressions

/-! Precision for arbitrary rational objectives over unit-coefficient LP
vertices. Only constraints are unit integral; objective entries are arbitrary
rationals. These are quantitative lemmas, not an optimization algorithm. -/
noncomputable section
namespace BuyAtBulk.PolynomialLP
open RationalLP Computation.Rational
open scoped BigOperators
variable {J C : Type} [Fintype J] [Fintype C] [DecidableEq J]

def objectiveBudget (dimension coefficientBits : ℕ) : ℕ :=
  2*(4*dimension+1)*(coefficientBits+(2*dimension^2+4)+5)+2

theorem linearForm_bits (form : (J → ℚ) →ₗ[ℚ] ℚ) (x : J → ℚ) (L K : ℕ)
    (coefficients : ∀ j, (Code.ofRat (form (Pi.single j 1))).bits ≤ L)
    (coordinates : ∀ j, (Code.ofRat (x j)).bits ≤ K) :
    (Code.ofRat (form x)).bits ≤ 2*(4*Fintype.card J+1)*(L+K+5)+2 := by
  classical
  let terms := (Finset.univ.toList : List J).map fun j => (form (Pi.single j 1),x j)
  have length : terms.length = Fintype.card J := by simp [terms]
  have encoded := Computation.HelperExpressions.sum_products_bits terms (L+K+5) (by omega) (by
    intro q member
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp member
    change (Code.ofRat (form (Pi.single j 1))).bits+1 ≤ L+K+5 ∧ (Code.ofRat (x j)).bits+1 ≤ L+K+5
    exact ⟨by have := coefficients j; omega, by have := coordinates j; omega⟩)
  have value : (terms.map fun q => q.1*q.2).sum = form x := by
    rw [linearForm_expansion form x]
    simp [terms, List.map_map, Function.comp_def]
  simpa only [length, value] using encoded

theorem vertex_objective_bits (P : Problem J C) (a : C → J → ℤ) (b : C → ℤ)
    (coefficients : ∀ i j, P.row i (Pi.single j 1) = (a i j : ℚ))
    (rhs : ∀ i, P.bound i = (b i : ℚ))
    (a_unit : ∀ i j, (a i j).natAbs ≤ 1) (b_unit : ∀ i, (b i).natAbs ≤ 1)
    (L : ℕ) (objective : ∀ j, (Code.ofRat (P.objective (Pi.single j 1))).bits ≤ L)
    (x : J → ℚ) (vertex : P.Vertex x) :
    (Code.ofRat (P.objective x)).bits ≤ objectiveBudget (Fintype.card J) L := by
  obtain ⟨code, decoded, bits⟩ := vertex_encoded P a b coefficients rhs a_unit b_unit x vertex
  apply linearForm_bits P.objective x L (2*(Fintype.card J)^2+4) objective
  intro j
  rw [← decoded j]
  exact (Code.normalized_bits_le _).trans (bits j)

theorem vertex_objective_gap (P : Problem J C) (a : C → J → ℤ) (b : C → ℤ)
    (coefficients : ∀ i j, P.row i (Pi.single j 1) = (a i j : ℚ))
    (rhs : ∀ i, P.bound i = (b i : ℚ))
    (a_unit : ∀ i j, (a i j).natAbs ≤ 1) (b_unit : ∀ i, (b i).natAbs ≤ 1)
    (L : ℕ) (objective : ∀ j, (Code.ofRat (P.objective (Pi.single j 1))).bits ≤ L)
    (x y : J → ℚ) (x_vertex : P.Vertex x) (y_vertex : P.Vertex y)
    (improves : P.objective x < P.objective y) :
    1/(2 : ℚ)^(2*(objectiveBudget (Fintype.card J) L+1)) ≤ P.objective y-P.objective x := by
  exact encoding_gap _ _ _ improves
    (vertex_objective_bits P a b coefficients rhs a_unit b_unit L objective x x_vertex)
    (vertex_objective_bits P a b coefficients rhs a_unit b_unit L objective y y_vertex)

/-- An interval narrower than the denominator gap contains at most one
rational of the promised encoding. This is a uniqueness result, not a search. -/
theorem encoding_interval_unique (lo hi q r : ℚ) (L : ℕ)
    (interval : hi-lo < 1/(2 : ℚ)^(2*(L+1)))
    (q_low : lo ≤ q) (q_high : q ≤ hi) (r_low : lo ≤ r) (r_high : r ≤ hi)
    (q_bits : (Code.ofRat q).bits ≤ L) (r_bits : (Code.ofRat r).bits ≤ L) : q = r := by
  rcases lt_trichotomy q r with less | equal | greater
  · have gap := encoding_gap q r L less q_bits r_bits
    linarith
  · exact equal
  · have gap := encoding_gap r q L greater r_bits q_bits
    linarith

end BuyAtBulk.PolynomialLP
