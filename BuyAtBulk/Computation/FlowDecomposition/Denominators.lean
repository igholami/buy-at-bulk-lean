import BuyAtBulk.Computation.FlowDecomposition.Correctness
import BuyAtBulk.Computation.Rational.Encoding
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! A single product of input denominators controls every extracted rational
weight. Bottlenecks select existing values, and subtraction preserves divisibility
by that denominator. There is no iterated denominator-growth assumption. -/
namespace BuyAtBulk.Computation.FlowDecomposition
variable {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

abbrev HasDenominator (D : ℕ) (q : ℚ) : Prop := q.den ∣ D

theorem sub_denominator (D : ℕ) (q r : ℚ) (hq : HasDenominator D q) (hr : HasDenominator D r) :
    HasDenominator D (q - r) :=
  (Rat.sub_den_dvd_lcm q r).trans (Nat.lcm_dvd hq hr)

theorem bottleneck_denominator {source target : V} (flow : V → V → ℚ)
    (mass : ℚ) (path : G.Path source target) (D : ℕ)
    (mass_den : HasDenominator D mass) (flow_den : ∀ u v, HasDenominator D (flow u v)) :
    HasDenominator D (bottleneck G flow mass path) := by
  have member : bottleneck G flow mass path ∈
      insert mass (path.val.darts.map fun dart => flow dart.fst dart.snd).toFinset := Finset.min'_mem _ _
  rcases Finset.mem_insert.mp member with equal | member
  · rw [equal]
    exact mass_den
  · obtain ⟨dart, _, equal⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    rw [← equal]
    exact flow_den dart.fst dart.snd

theorem subtract_denominator {source target : V} (matrix : FlowMatrix n) (amount : ℚ)
    (path : G.Path source target) (D : ℕ) (amount_den : HasDenominator D amount)
    (matrix_den : ∀ u v, HasDenominator D (decodedFlow numbering matrix u v)) :
    ∀ u v, HasDenominator D (decodedFlow numbering (subtract G numbering matrix amount path) u v) := by
  intro u v
  simp only [subtract, decodedFlow, matrixFlow, Vector.getElem_ofFn, Equiv.symm_apply_apply]
  split
  · exact sub_denominator D _ _ (matrix_den u v) amount_den
  · simpa [decodedFlow, matrixFlow] using matrix_den u v

theorem extract_denominator (source target : V) (fuel : ℕ) :
    ∀ (matrix : FlowMatrix n) (mass : ℚ) (D : ℕ) (entries : WeightedPaths G source target),
      HasDenominator D mass → (∀ u v, HasDenominator D (decodedFlow numbering matrix u v)) →
      extract G numbering source target fuel matrix mass = some entries →
      ∀ entry ∈ entries, HasDenominator D entry.1 := by
  induction fuel with
  | zero =>
    intro matrix mass D entries hm hf returned
    simp only [extract] at returned
    split at returned
    · have equal := Option.some.inj returned
      subst entries
      simp
    · contradiction
  | succ fuel ih =>
    intro matrix mass D entries hm hf returned
    simp only [extract] at returned
    split at returned
    · have equal := Option.some.inj returned
      subst entries
      simp
    · split at returned
      · contradiction
      · rename_i path found
        let amount := bottleneck G (decodedFlow numbering matrix) mass path
        have amount_den : HasDenominator D amount := bottleneck_denominator G _ _ path D hm hf
        obtain ⟨rest, computed, equal⟩ := Option.map_eq_some_iff.mp returned
        subst entries
        have tail_den := ih (subtract G numbering matrix amount path) (mass - amount) D rest
          (sub_denominator D mass amount hm amount_den) (subtract_denominator G numbering matrix amount path D amount_den hf) computed
        intro entry member
        rcases List.mem_cons.mp member with rfl | member
        · exact amount_den
        · exact tail_den entry member

/-- A computable common integer denominator for a stored rational matrix. -/
def commonDenominator (matrix : FlowMatrix n) : ℕ :=
  ∏ index : Fin n × Fin n, (matrixFlow matrix index.1 index.2).den

def denominatorInputBits (matrix : FlowMatrix n) : ℕ :=
  ∑ index : Fin n × Fin n, (matrixFlow matrix index.1 index.2).den.size

theorem commonDenominator_pos (matrix : FlowMatrix n) : 0 < commonDenominator matrix :=
  Finset.prod_pos fun _ _ => Rat.den_pos _

theorem coordinate_denominator (matrix : FlowMatrix n) (u v : Fin n) :
    HasDenominator (commonDenominator matrix) (matrixFlow matrix u v) := by
  exact Finset.dvd_prod_of_mem (fun index : Fin n × Fin n => (matrixFlow matrix index.1 index.2).den)
    (Finset.mem_univ (u, v))

theorem decoded_coordinate_denominator (matrix : FlowMatrix n) (u v : V) :
    HasDenominator (commonDenominator matrix) (decodedFlow numbering matrix u v) :=
  coordinate_denominator matrix (numbering u) (numbering v)

theorem commonDenominator_bits (matrix : FlowMatrix n) :
    (commonDenominator matrix).size ≤ denominatorInputBits matrix + 1 := by
  have bound : ∀ indices : Finset (Fin n × Fin n),
      (∏ index ∈ indices, (matrixFlow matrix index.1 index.2).den) ≤
        2 ^ (∑ index ∈ indices, (matrixFlow matrix index.1 index.2).den.size) := by
    intro indices
    induction indices using Finset.induction_on with
    | empty => simp
    | @insert index indices missing ih =>
      rw [Finset.prod_insert missing, Finset.sum_insert missing, pow_add]
      exact Nat.mul_le_mul (Nat.lt_size_self _).le ih
  apply Nat.size_le.mpr
  have upper := bound Finset.univ
  change commonDenominator matrix ≤ 2 ^ denominatorInputBits matrix at upper
  apply upper.trans_lt
  rw [pow_succ]
  have positive : 0 < 2 ^ denominatorInputBits matrix := Nat.two_pow_pos _
  omega

/-- Unit-interval rationals with a common denominator have bounded normalized
integer components. Both signs and the empty numerator are handled exactly. -/
theorem unit_components_bound (q : ℚ) (D : ℕ) (positive : 0 < D)
    (denominator : HasDenominator D q) (lower : 0 ≤ q) (upper : q ≤ 1) :
    q.num.natAbs ≤ D ∧ q.den ≤ D := by
  have den_le : q.den ≤ D := Nat.le_of_dvd positive denominator
  have qdenpos : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have quotient : (q.num : ℚ) / (q.den : ℚ) ≤ 1 := by simpa only [Rat.num_div_den] using upper
  have numeratorQ : (q.num : ℚ) ≤ q.den := (div_le_one qdenpos).mp quotient
  have numeratorZ : q.num ≤ (q.den : ℤ) := by exact_mod_cast numeratorQ
  have num_nonneg : 0 ≤ q.num := Rat.num_nonneg.mpr lower
  have numeratorNat : q.num.natAbs ≤ q.den := by
    exact_mod_cast (show (q.num.natAbs : ℤ) ≤ (q.den : ℤ) by
      rw [Int.natAbs_of_nonneg num_nonneg]
      exact numeratorZ)
  exact ⟨numeratorNat.trans den_le, den_le⟩

theorem unit_bits_bound (q : ℚ) (D : ℕ) (positive : 0 < D)
    (denominator : HasDenominator D q) (lower : 0 ≤ q) (upper : q ≤ 1) :
    (Rational.Code.ofRat q).bits ≤ 2 * D.size + 2 := by
  obtain ⟨num, den⟩ := unit_components_bound q D positive denominator lower upper
  have nbits := Nat.size_le_size num
  have dbits := Nat.size_le_size den
  simp only [Rational.Code.bits, Rational.Code.ofRat, Int.natAbs_natCast]
  omega

/-- Natural numerator of a nonnegative rational at the fixed common scale.
The denominator itself never appears as an iteration bound. -/
def scaledNumerator (D : ℕ) (q : ℚ) : ℕ := q.num.natAbs * (D / q.den)

theorem scaledNumerator_value (q : ℚ) (D : ℕ) (positive : 0 < D)
    (denominator : HasDenominator D q) (lower : 0 ≤ q) :
    (scaledNumerator D q : ℚ) / D = q := by
  have den_le : q.den ≤ D := Nat.le_of_dvd positive denominator
  have quotient_pos : 0 < D / q.den := Nat.div_pos den_le q.den_pos
  have quotient_nonzero : ((D / q.den : ℕ) : ℚ) ≠ 0 := by exact_mod_cast quotient_pos.ne'
  have factor : (q.den : ℚ) * ((D / q.den : ℕ) : ℚ) = D := by
    exact_mod_cast Nat.mul_div_cancel' denominator
  have nonnegative : 0 ≤ q.num := Rat.num_nonneg.mpr lower
  have numerator : (q.num.natAbs : ℚ) = q.num := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) (Int.natAbs_of_nonneg nonnegative)
  simp only [scaledNumerator, Nat.cast_mul]
  rw [numerator, ← factor, mul_div_mul_right _ _ quotient_nonzero, Rat.num_div_den]

theorem scaledNumerator_le (q : ℚ) (D : ℕ) (positive : 0 < D)
    (denominator : HasDenominator D q) (lower : 0 ≤ q) (upper : q ≤ 1) :
    scaledNumerator D q ≤ D := by
  have bound : (scaledNumerator D q : ℚ) / D ≤ 1 := by
    rw [scaledNumerator_value q D positive denominator lower]
    exact upper
  have posQ : (0 : ℚ) < D := by exact_mod_cast positive
  exact_mod_cast (div_le_one posQ).mp bound

/-- At the common scale the actual rational update is exactly natural
subtraction. Thus the fixed-D representation is preserved by every update. -/
theorem scaledNumerator_sub (q r : ℚ) (D : ℕ) (positive : 0 < D)
    (hq : HasDenominator D q) (hr : HasDenominator D r)
    (lower : 0 ≤ r) (order : r ≤ q) :
    scaledNumerator D (q - r) = scaledNumerator D q - scaledNumerator D r := by
  have qnonneg := lower.trans order
  have subnonneg := sub_nonneg.mpr order
  have subden := sub_denominator D q r hq hr
  have nonzero : (D : ℚ) ≠ 0 := by exact_mod_cast positive.ne'
  have equation : (scaledNumerator D (q - r) : ℚ) =
      (scaledNumerator D q : ℚ) - (scaledNumerator D r : ℚ) := by
    apply (div_left_inj' nonzero).mp
    rw [sub_div, scaledNumerator_value _ _ positive subden subnonneg,
      scaledNumerator_value _ _ positive hq qnonneg, scaledNumerator_value _ _ positive hr lower]
  have scaled_order : scaledNumerator D r ≤ scaledNumerator D q := by
    have nonnegative : (0 : ℚ) ≤ scaledNumerator D (q - r) := Nat.cast_nonneg _
    have rational_order : (scaledNumerator D r : ℚ) ≤ scaledNumerator D q := by linarith
    exact_mod_cast rational_order
  have same : (scaledNumerator D (q - r) : ℚ) =
      ((scaledNumerator D q - scaledNumerator D r : ℕ) : ℚ) := by
    rw [Nat.cast_sub scaled_order]
    exact equation
  exact_mod_cast same

end BuyAtBulk.Computation.FlowDecomposition
