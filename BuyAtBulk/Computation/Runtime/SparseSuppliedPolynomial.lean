import BuyAtBulk.Computation.Runtime.SparseSupplied
import BuyAtBulk.Computation.Runtime.SparseSuppliedEncoding
import BuyAtBulk.Computation.Runtime.SuppliedPolynomial

/-! Polynomial certificates for executed supplied-path sparsification, measured
in the complete supplied-input encoding. -/
set_option maxHeartbeats 16000000
set_option maxRecDepth 65536
namespace BuyAtBulk.Computation.Runtime.SparseSupplied
open Rational StoredOriginal PolynomialBudget
namespace Polynomial

def parameters (n h k L : ℕ) (i : Fin 4) : ℕ :=
  if i=0 then n else if i=1 then h else if i=2 then k else L

def requestCountCertificate (n h k L : ℕ) :
    Certificate (parameters n h k L) (5*k+1+compressCount n k) := by
  original_poly_cert

def requestWordsCertificate (n h k L : ℕ) :
    Certificate (parameters n h k L) (n+h+L+1+compressWords n k L) := by
  original_poly_cert

def requestCountTerm : Term 4 := (requestCountCertificate 0 0 0 0).term
def requestWordsTerm : Term 4 := (requestWordsCertificate 0 0 0 0).term

theorem term_bound (term : Term 4) (n h k L S : ℕ)
    (hn : n≤S) (hh : h≤S) (hk : k≤S) (hL : L≤S+8) :
    term.eval (parameters n h k L)≤(term.weight*9^term.degree)*(S+1)^term.degree := by
  have inputs : ∀ i,parameters n h k L i≤8*(S+1) := by
    intro i
    simp only[parameters]
    split_ifs <;>omega
  calc
    _ ≤ term.weight*(8*(S+1)+1)^term.degree := term.eval_le _ _ inputs
    _ ≤ term.weight*(9*(S+1))^term.degree :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ = _ := by rw[mul_pow];ring

def outputBudget (n h k L : ℕ) : ℕ :=
  L+2*(h*(n*n+1))+16+(h*(n*n+1))*entryBitBudget n h (2*n*n*cellBits n k L+4)

def countCertificate (n h k L : ℕ) :
    Certificate (parameters n h k L) (runCount n k h) := by original_poly_cert

def wordsCertificate (n h k L : ℕ) :
    Certificate (parameters n h k L) (runWords n k h L) := by original_poly_cert

def outputCertificate (n h k L : ℕ) :
    Certificate (parameters n h k L) (outputBudget n h k L) := by original_poly_cert

def countTerm : Term 4 := (countCertificate 0 0 0 0).term
def wordsTerm : Term 4 := (wordsCertificate 0 0 0 0).term
def outputTerm : Term 4 := (outputCertificate 0 0 0 0).term

variable {n resources h : ℕ} (tables : Tables n resources h) (fractional : Fractional tables)

theorem count_bound : runCount n fractional.entries.length h ≤
    (countTerm.weight*9^countTerm.degree)*(SuppliedEncoding.inputSize tables fractional 8 1+1)^countTerm.degree := by
  have dims := SuppliedEncoding.dimensions tables fractional 8 1
  have entries := SuppliedEncoding.entries_count tables fractional 8 1
  exact (countCertificate n h fractional.entries.length
    (SuppliedEncoding.inputSize tables fractional 8 1+8)).correct.symm.trans_le
      (term_bound countTerm _ _ _ _ _ (by omega) (by omega) entries le_rfl)

theorem words_bound : runWords n fractional.entries.length h (SuppliedEncoding.inputSize tables fractional 8 1+8) ≤
    (wordsTerm.weight*9^wordsTerm.degree)*(SuppliedEncoding.inputSize tables fractional 8 1+1)^wordsTerm.degree := by
  have dims := SuppliedEncoding.dimensions tables fractional 8 1
  have entries := SuppliedEncoding.entries_count tables fractional 8 1
  exact (wordsCertificate n h fractional.entries.length
    (SuppliedEncoding.inputSize tables fractional 8 1+8)).correct.symm.trans_le
      (term_bound wordsTerm _ _ _ _ _ (by omega) (by omega) entries le_rfl)

theorem output_bound : outputBudget n h fractional.entries.length (SuppliedEncoding.inputSize tables fractional 8 1+8) ≤
    (outputTerm.weight*9^outputTerm.degree)*(SuppliedEncoding.inputSize tables fractional 8 1+1)^outputTerm.degree := by
  have dims := SuppliedEncoding.dimensions tables fractional 8 1
  have entries := SuppliedEncoding.entries_count tables fractional 8 1
  exact (outputCertificate n h fractional.entries.length
    (SuppliedEncoding.inputSize tables fractional 8 1+8)).correct.symm.trans_le
      (term_bound outputTerm _ _ _ _ _ (by omega) (by omega) entries le_rfl)

end Polynomial

/-- Constructive sparse path decomposition, including polynomial execution and
binary output size in the complete supplied path-list input. -/
def SuppliedSparsePolynomialTarget : Prop :=
  ∃ C d W e O f : ℕ, ∀ (n resources h : ℕ) (tables : Tables n resources h)
    (fractional : Fractional tables),
    ∃ output : Fractional tables,
      (storedRun tables fractional).value=some output.entries ∧
      output.opening=fractional.opening ∧ output.entries.length ≤ h*(n*n+1) ∧
      (∀ entry∈output.entries,0<entry.2.1) ∧
      OriginalPipeline.buyingBudget tables.graphData (output.decode tables)=
        OriginalPipeline.buyingBudget tables.graphData (fractional.decode tables) ∧
      (∀ i,OriginalPipeline.fractionalLength tables.graphData (output.decode tables) i ≤
        OriginalPipeline.fractionalLength tables.graphData (fractional.decode tables) i) ∧
      OriginalPipeline.rentalBudget tables.graphData (output.decode tables) ≤
        OriginalPipeline.rentalBudget tables.graphData (fractional.decode tables) ∧
      (storedRun tables fractional).events.length ≤ C*(SuppliedEncoding.inputSize tables fractional 8 1+1)^d ∧
      WordsWithin (W*(SuppliedEncoding.inputSize tables fractional 8 1+1)^e) (storedRun tables fractional).events ∧
      SuppliedEncoding.inputSize tables output 8 1 ≤ O*(SuppliedEncoding.inputSize tables fractional 8 1+1)^f

theorem supplied_sparse_polynomial : SuppliedSparsePolynomialTarget := by
  refine ⟨Polynomial.countTerm.weight*9^Polynomial.countTerm.degree,Polynomial.countTerm.degree,
    Polynomial.wordsTerm.weight*9^Polynomial.wordsTerm.degree,Polynomial.wordsTerm.degree,
    Polynomial.outputTerm.weight*9^Polynomial.outputTerm.degree,Polynomial.outputTerm.degree,?_⟩
  intro n resources h tables fractional
  let S := SuppliedEncoding.inputSize tables fractional 8 1
  let L := S+8
  obtain ⟨output,returned,opening,support,positive,buying,lengths,rental,bits,count,words⟩ :=
    storedRun_correct tables fractional L (by dsimp[L];omega)
      (fun entry member => (SuppliedEncoding.weight_bits tables fractional 8 1 entry member).trans (by dsimp[L,S];omega))
  refine ⟨output,returned,opening,support,positive,buying,lengths,rental,
    count.trans (Polynomial.count_bound tables fractional),
    words.mono (Polynomial.words_bound tables fractional),?_⟩
  have encoded := output_encoding_bound tables fractional output opening (h*(n*n+1))
    (2*n*n*cellBits n fractional.entries.length L+4) support bits
  apply (encoded.trans ?_).trans (Polynomial.output_bound tables fractional)
  dsimp [Polynomial.outputBudget,L,S]
  omega
end BuyAtBulk.Computation.Runtime.SparseSupplied
