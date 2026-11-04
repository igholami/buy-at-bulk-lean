import BuyAtBulk.Computation.Runtime.RoundingPolynomial

/-! Uniform polynomial running time for arbitrary binary-encoded rounding
parameters. Their magnitudes do not occur in the operation bound; their binary
lengths are included among the input scalar lengths. -/
namespace BuyAtBulk.Computation.Runtime.StoredRounding
open Rational RoundingPolynomial

/-- Fixed constants for every stored graph and both supplied parameters.
Rational/integer operations and all intermediate words use Primitive's model. -/
def ParameterizedPolynomialTarget : Prop :=
    ∃ C d W e : ℕ, ∀ (n h : ℕ) (input : ShortestPath.GraphEncoding n)
      (buying physical opening : Vector ℚ n) (budget : ℚ)
      (source target : Vector (Fin n) h) (lengths : Vector ℚ h)
      (ratio r : ℕ) (ratio_ge : 2 ≤ ratio) (L : ℕ), 8 ≤ L →
      (∀ v : Fin n, (Code.ofRat buying[v.val]).bits ≤ L) →
      (∀ v : Fin n, (Code.ofRat physical[v.val]).bits ≤ L) →
      (∀ v : Fin n, (Code.ofRat opening[v.val]).bits ≤ L) →
      (Code.ofRat budget).bits ≤ L →
      (∀ i : Fin h, (Code.ofRat lengths[i.val]).bits ≤ L) →
      ratio.size ≤ L → r.size ≤ L →
      (run input buying physical opening budget source target lengths ratio r ratio_ge).events.length ≤ C*(n+h+L+1)^d ∧
      WordsWithin (W*(n+h+L+1)^e)
        (run input buying physical opening budget source target lengths ratio r ratio_ge).events

theorem parameterized_polynomial : ParameterizedPolynomialTarget := by
  refine ⟨roundingCountTerm.weight,roundingCountTerm.degree,
    roundingWordsTerm.weight,roundingWordsTerm.degree,?_⟩
  intro n h input buying physical opening budget source target lengths ratio r ratio_ge L constant bw pw ow Bw lw rw sw
  constructor
  · exact (run_count input buying physical opening budget source target lengths ratio r ratio_ge).trans
      (roundingCount_bound (S:=n+h+L) (by omega) (by omega))
  · exact (run_words input buying physical opening budget source target lengths ratio r ratio_ge L constant bw pw ow Bw lw rw sw).mono
      (roundingWords_bound (S:=n+h+L) (by omega) (by omega) (by omega))

end BuyAtBulk.Computation.Runtime.StoredRounding
