import BuyAtBulk.Computation.Runtime.SuppliedRounding
import BuyAtBulk.Computation.Runtime.SuppliedEncoding
import BuyAtBulk.Computation.Runtime.OriginalPolynomial

/-! End-to-end polynomial rounding of a supplied feasible original path LP,
with arbitrary binary parameters. All bounds use the full encoded input. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 65536
namespace BuyAtBulk.Computation.Runtime.Supplied
open Rational BuyAtBulk.Computation.StoredOriginal PolynomialBudget
namespace Polynomial

def parameters (n resources h k L : ℕ) (i : Fin 5) : ℕ :=
  if i=0 then n else if i=1 then resources else if i=2 then h else if i=3 then k else L

def countCertificate (n resources h k L : ℕ) :
    Certificate (parameters n resources h k L) (countBudget n resources h k) := by
  original_poly_cert

def wordsCertificate (n resources h k L : ℕ) :
    Certificate (parameters n resources h k L) (wordBudget n resources h k L) := by
  original_poly_cert

def countTerm : Term 5 := (countCertificate 0 0 0 0 0).term
def wordsTerm : Term 5 := (wordsCertificate 0 0 0 0 0).term

private theorem term_bound (term : Term 5) (n resources h k L S : ℕ)
    (hn : n≤S) (hr : resources≤S) (hh : h≤S) (hk : k≤S) (hL : L≤S+8) :
    term.eval (parameters n resources h k L)≤(term.weight*9^term.degree)*(S+1)^term.degree := by
  have inputs : ∀ i,parameters n resources h k L i≤8*(S+1) := by
    intro i
    simp only[parameters]
    split_ifs <;>omega
  calc
    _ ≤ term.weight*(8*(S+1)+1)^term.degree := term.eval_le _ _ inputs
    _ ≤ term.weight*(9*(S+1))^term.degree :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ = _ := by rw[mul_pow];ring

variable {n resources h : ℕ} (tables : Tables n resources h) (fractional : Fractional tables) (ratio r : ℕ)

theorem count_bound : countBudget n resources h fractional.entries.length ≤
    (countTerm.weight*9^countTerm.degree)*(SuppliedEncoding.inputSize tables fractional ratio r+1)^countTerm.degree := by
  have dims := SuppliedEncoding.dimensions tables fractional ratio r
  have entries := SuppliedEncoding.entries_count tables fractional ratio r
  exact (countCertificate n resources h fractional.entries.length
    (SuppliedEncoding.inputSize tables fractional ratio r+8)).correct.symm.trans_le
      (term_bound countTerm _ _ _ _ _ _ (by omega) (by omega) (by omega) entries le_rfl)

theorem words_bound : wordBudget n resources h fractional.entries.length (SuppliedEncoding.inputSize tables fractional ratio r+8) ≤
    (wordsTerm.weight*9^wordsTerm.degree)*(SuppliedEncoding.inputSize tables fractional ratio r+1)^wordsTerm.degree := by
  have dims := SuppliedEncoding.dimensions tables fractional ratio r
  have entries := SuppliedEncoding.entries_count tables fractional ratio r
  exact (wordsCertificate n resources h fractional.entries.length
    (SuppliedEncoding.inputSize tables fractional ratio r+8)).correct.symm.trans_le
      (term_bound wordsTerm _ _ _ _ _ _ (by omega) (by omega) (by omega) entries le_rfl)

end Polynomial

/-- The same supplied-input computation returns supported original routes,
preserves both LP budgets up to the parameterized factors, and has polynomial
operation count and intermediate word lengths in the complete binary input. -/
def SuppliedPolynomialTarget : Prop :=
  ∃ C d W e : ℕ, ∀ (n resources h : ℕ) (tables : Tables n resources h)
    (fractional : Fractional tables) (ratio r : ℕ) (ratio_ge : 8≤ratio) (r_ge : 1≤r),
    (∃ output,(run tables fractional ratio r (by omega)).value=some output ∧
      OutputSpec tables fractional ratio r output) ∧
    (run tables fractional ratio r (by omega)).events.length≤
      C*(SuppliedEncoding.inputSize tables fractional ratio r+1)^d ∧
    WordsWithin (W*(SuppliedEncoding.inputSize tables fractional ratio r+1)^e)
      (run tables fractional ratio r (by omega)).events

theorem supplied_polynomial : SuppliedPolynomialTarget := by
  refine ⟨Polynomial.countTerm.weight*9^Polynomial.countTerm.degree,Polynomial.countTerm.degree,
    Polynomial.wordsTerm.weight*9^Polynomial.wordsTerm.degree,Polynomial.wordsTerm.degree,?_⟩
  intro n resources h tables fractional ratio r ratio_ge r_ge
  let S := SuppliedEncoding.inputSize tables fractional ratio r
  let L := S+8
  have count := run_count tables fractional ratio r ratio_ge r_ge
  have words := run_words tables fractional ratio r (by omega) L (by dsimp[L];omega)
    (fun a => (SuppliedEncoding.buying_bits tables fractional ratio r a).trans (by dsimp[L,S];omega))
    (fun a => (SuppliedEncoding.physical_bits tables fractional ratio r a).trans (by dsimp[L,S];omega))
    (fun i => (SuppliedEncoding.demand_bits tables fractional ratio r i).trans (by dsimp[L,S];omega))
    (fun a => (SuppliedEncoding.opening_bits tables fractional ratio r a).trans (by dsimp[L,S];omega))
    (fun entry member => (SuppliedEncoding.weight_bits tables fractional ratio r entry member).trans (by dsimp[L,S];omega))
    ((SuppliedEncoding.ratio_bits tables fractional ratio r).trans (by dsimp[L,S];omega))
    ((SuppliedEncoding.girth_bits tables fractional ratio r).trans (by dsimp[L,S];omega))
  exact ⟨run_correct tables fractional ratio r ratio_ge r_ge,
    count.trans (Polynomial.count_bound tables fractional ratio r),
    words.mono (Polynomial.words_bound tables fractional ratio r)⟩

end BuyAtBulk.Computation.Runtime.Supplied
