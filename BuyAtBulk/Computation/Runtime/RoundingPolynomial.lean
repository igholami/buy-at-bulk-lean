import BuyAtBulk.Computation.Runtime.PolynomialBudget
import BuyAtBulk.Computation.Runtime.OriginalRoundPrepared

/-! Kernel-checked fixed polynomial certificates for the complete numerical
rounder, compact-flow metadata bridge, and original path projection. -/
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 8192
namespace BuyAtBulk.Computation.Runtime
open PolynomialBudget

namespace RoundingPolynomial

def two (n h : ℕ) (i : Fin 2) : ℕ := if i=0 then n else h

def three (n h L : ℕ) (i : Fin 3) : ℕ := if i=0 then n else if i=1 then h else L

def five (n r h m L : ℕ) (i : Fin 5) : ℕ :=
  if i=0 then n else if i=1 then r else if i=2 then h else if i=3 then m else L

def coreCount (n h : ℕ) : Certificate (two n h) (StoredCore.coreCount n h) := by poly_cert

def coreWords (n h L : ℕ) : Certificate (three n h L) (StoredCore.coreWords n h L) := by poly_cert

def roundingCount (n h : ℕ) : Certificate (two n h) (StoredRounding.roundingCount n h) := by poly_cert

def roundingWords (n h L : ℕ) : Certificate (three n h L) (StoredRounding.roundingWords n h L) := by poly_cert

def optimizedCount (n h : ℕ) : Certificate (two n h) (StoredRounding.optimizedCount n h) := by poly_cert

def optimizedWords (n h L : ℕ) : Certificate (three n h L) (StoredRounding.optimizedWords n h L) := by poly_cert

def compactCount (n h : ℕ) : Certificate (two n h) (StoredCompactRounding.countBudget n h) := by poly_cert

def compactWords (n h L : ℕ) : Certificate (three n h L) (StoredCompactRounding.wordBudget n h L) := by poly_cert

def originalCount (n r h m L : ℕ) : Certificate (five n r h m L) (Original.roundPreparedCount r h m) := by poly_cert

def originalWords (n r h m L : ℕ) : Certificate (five n r h m L) (Original.roundPreparedWords n r h m L) := by poly_cert


theorem three_bound {n h L S : ℕ} (hn : n≤S) (hh : h≤S) (hL : L≤S) : ∀ i,three n h L i≤S := by
  intro i
  simp only[three]
  split_ifs <;>assumption


theorem two_bound {n h S : ℕ} (hn : n≤S) (hh : h≤S) : ∀ i,two n h i≤S := by
  intro i
  simp only[two]
  split_ifs <;>assumption

/-- These syntax trees are closed constants: their coefficients and degrees
are independent of the supplied graph dimensions and coefficient widths. -/
def roundingCountTerm : Term 2 := (roundingCount 0 0).term

def roundingWordsTerm : Term 3 := (roundingWords 0 0 0).term

def optimizedCountTerm : Term 2 := (optimizedCount 0 0).term

def optimizedWordsTerm : Term 3 := (optimizedWords 0 0 0).term

def compactCountTerm : Term 2 := (compactCount 0 0).term

def compactWordsTerm : Term 3 := (compactWords 0 0 0).term

def originalCountTerm : Term 5 := (originalCount 0 0 0 0 0).term

def originalWordsTerm : Term 5 := (originalWords 0 0 0 0 0).term

@[simp] theorem roundingCount_eval (n h : ℕ) : roundingCountTerm.eval (two n h)=StoredRounding.roundingCount n h := by exact (roundingCount n h).correct
@[simp] theorem roundingWords_eval (n h L : ℕ) : roundingWordsTerm.eval (three n h L)=StoredRounding.roundingWords n h L := by exact (roundingWords n h L).correct
@[simp] theorem optimizedCount_eval (n h : ℕ) : optimizedCountTerm.eval (two n h)=StoredRounding.optimizedCount n h := by exact (optimizedCount n h).correct
@[simp] theorem optimizedWords_eval (n h L : ℕ) : optimizedWordsTerm.eval (three n h L)=StoredRounding.optimizedWords n h L := by exact (optimizedWords n h L).correct
@[simp] theorem compactCount_eval (n h : ℕ) : compactCountTerm.eval (two n h)=StoredCompactRounding.countBudget n h := by exact (compactCount n h).correct
@[simp] theorem compactWords_eval (n h L : ℕ) : compactWordsTerm.eval (three n h L)=StoredCompactRounding.wordBudget n h L := by exact (compactWords n h L).correct
@[simp] theorem originalCount_eval (n r h m L : ℕ) : originalCountTerm.eval (five n r h m L)=Original.roundPreparedCount r h m := by exact (originalCount n r h m L).correct
@[simp] theorem originalWords_eval (n r h m L : ℕ) : originalWordsTerm.eval (five n r h m L)=Original.roundPreparedWords n r h m L := by exact (originalWords n r h m L).correct

theorem roundingCount_bound {n h S : ℕ} (hn : n≤S) (hh : h≤S) :
    StoredRounding.roundingCount n h≤roundingCountTerm.weight*(S+1)^roundingCountTerm.degree :=
  (roundingCount n h).bound S (two_bound hn hh)

theorem roundingWords_bound {n h L S : ℕ} (hn : n≤S) (hh : h≤S) (hL : L≤S) :
    StoredRounding.roundingWords n h L≤roundingWordsTerm.weight*(S+1)^roundingWordsTerm.degree :=
  (roundingWords n h L).bound S (three_bound hn hh hL)

theorem optimizedCount_bound {n h S : ℕ} (hn : n≤S) (hh : h≤S) :
    StoredRounding.optimizedCount n h≤optimizedCountTerm.weight*(S+1)^optimizedCountTerm.degree :=
  (optimizedCount n h).bound S (two_bound hn hh)

theorem optimizedWords_bound {n h L S : ℕ} (hn : n≤S) (hh : h≤S) (hL : L≤S) :
    StoredRounding.optimizedWords n h L≤optimizedWordsTerm.weight*(S+1)^optimizedWordsTerm.degree :=
  (optimizedWords n h L).bound S (three_bound hn hh hL)

theorem compactCount_bound {n h S : ℕ} (hn : n≤S) (hh : h≤S) :
    StoredCompactRounding.countBudget n h≤compactCountTerm.weight*(S+1)^compactCountTerm.degree :=
  (compactCount n h).bound S (two_bound hn hh)

theorem compactWords_bound {n h L S : ℕ} (hn : n≤S) (hh : h≤S) (hL : L≤S) :
    StoredCompactRounding.wordBudget n h L≤compactWordsTerm.weight*(S+1)^compactWordsTerm.degree :=
  (compactWords n h L).bound S (three_bound hn hh hL)

end RoundingPolynomial
end BuyAtBulk.Computation.Runtime
