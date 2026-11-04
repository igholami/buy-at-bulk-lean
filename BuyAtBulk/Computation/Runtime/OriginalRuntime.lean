import BuyAtBulk.Computation.Runtime.OriginalTrace
import BuyAtBulk.Computation.Runtime.OriginalInputBits
import BuyAtBulk.Computation.Runtime.PolynomialBudget

/-! End-to-end resource bounds for the actual closed original graph program. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace BuyAtBulk.Computation.Runtime.Original
open Rational BuyAtBulk.Computation.StoredOriginal
variable {n resources requests : ℕ} (tables : Tables n resources requests)

def computationCount (n r h m L : ℕ) := checkedInitializationCount n r h+
  cachedCount n r h m+PolynomialLP.CompactEncoding.solveCount m h L+roundPreparedCount r h m+10

def intermediateBits (m h L : ℕ) := PolynomialLP.CompactEncoding.solutionBits m h L+L+2

def computationWords (n r h m L : ℕ) := initializationWords n r h+
  cachedWordBudget n r h L+PolynomialLP.CompactEncoding.solveWords m h L+
  roundPreparedWords n r h m (intermediateBits m h L)+n+r+h+m+L+20

theorem sourceTrace_runtime :
    (sourceTrace tables).events.length ≤ computationCount n resources requests
      (cachedBuffers tables).value.count (originalLeafBudget tables) ∧
    WordsWithin (computationWords n resources requests (cachedBuffers tables).value.count (originalLeafBudget tables))
      (sourceTrace tables).events := by
  let prepared := (cachedBuffers tables).value
  let L := originalLeafBudget tables
  let K := computationWords n resources requests prepared.count L
  have constant : 8 ≤ L := originalLeafBudget_constant tables
  have buying := cachedData_buying_bits tables
  have physical := cachedData_physical_bits tables
  have demand := cachedData_demand_bits tables
  have solver := PolynomialLP.CompactEncoding.solveTrace_runtime (prepared.data tables) L buying physical demand
  have initCount := initializeCheckedTrace_count tables
  have cacheCount := cachedBuffers_count tables
  rw [←cachedBuffers_count_value] at cacheCount
  have initWords := (initializeCheckedTrace_words tables).mono
    (show initializationWords n resources requests ≤ K by dsimp[K,computationWords];omega)
  have cacheWords := (cachedBuffers_words_polynomial tables L
    (fun a=>(inputSize_buying tables a).trans (by dsimp[L,originalLeafBudget];omega))
    (fun a=>(inputSize_length tables a).trans (by dsimp[L,originalLeafBudget];omega))
    (fun i=>(inputSize_demand tables i).trans (by dsimp[L,originalLeafBudget];omega))).mono
      (show cachedWordBudget n resources requests L ≤ K by dsimp[K,computationWords];omega)
  have solveWords := solver.2.2.mono
    (show PolynomialLP.CompactEncoding.solveWords prepared.count requests L ≤ K by dsimp[K,computationWords];omega)
  have one : 1 ≤ K := by dsimp[K,computationWords];omega
  have index (i : Fin requests) : i.val.size ≤ K :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := i.isLt;dsimp[K,computationWords];omega)
  unfold sourceTrace
  dsimp only
  cases initialized : (initializeCheckedTrace tables).value with
  | error i=>
    simp only [List.length_append,List.length_cons,List.length_nil]
    constructor
    · dsimp only [computationCount];omega
    · simpa only [wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
        or_false,forall_eq_or_imp,forall_eq,and_true] using And.intro initWords (And.intro one (index i))
  | ok fractional=>
    have actualInit : initializeChecked tables=.ok fractional := by rw [←initializeCheckedTrace_value];exact initialized
    obtain ⟨point,solved,f,same,coordinates,_,_⟩ := solvePrepared_correct tables prepared rfl fractional
    have traceSolved : (solvePreparedTrace tables prepared).value=some point := by rw[solvePreparedTrace_value];exact solved
    rw [traceSolved]
    have roundCount := roundPrepared_count tables prepared rfl f same point coordinates
    have pointBits := PolynomialLP.CompactEncoding.solve_output_bits (prepared.data tables) L buying physical demand point solved
    have roundWords := (roundPrepared_words tables prepared rfl f same point coordinates
      (intermediateBits prepared.count requests L) (by dsimp[intermediateBits];omega)
      (fun j=>(Nat.add_le_add_right (pointBits j) 1).trans (by dsimp[intermediateBits];omega))
      (fun v=>(Nat.add_le_add_right (buying v) 1).trans (by dsimp[intermediateBits];omega))
      (fun v=>(Nat.add_le_add_right (physical v) 1).trans (by dsimp[intermediateBits];omega))).mono
      (show roundPreparedWords n resources requests prepared.count (intermediateBits prepared.count requests L) ≤ K by dsimp[K,computationWords];omega)
    constructor
    · simp only [List.length_append,List.length_cons,List.length_nil]
      change _ ≤ computationCount n resources requests prepared.count L
      have solveCount : (solvePreparedTrace tables prepared).events.length ≤ PolynomialLP.CompactEncoding.solveCount prepared.count requests L := solver.2.1
      dsimp only [prepared] at solveCount roundCount
      dsimp only [computationCount,prepared]
      omega
    · change WordsWithin K _
      simpa only [prepared,solvePreparedTrace,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
        or_false,forall_eq_or_imp,forall_eq,and_true] using
        And.intro (And.intro (And.intro (And.intro (And.intro (And.intro initWords one) cacheWords) solveWords) one) roundWords) one

theorem closedTrace_runtime :
    (closedTrace tables).value=closedRun tables ∧
    (closedTrace tables).events.length ≤ computationCount n resources requests
      (cachedBuffers tables).value.count (originalLeafBudget tables)+3 ∧
    WordsWithin (computationWords n resources requests (cachedBuffers tables).value.count (originalLeafBudget tables))
      (closedTrace tables).events := by
  refine ⟨closedTrace_value tables,?_⟩
  have runtime := sourceTrace_runtime tables
  let K := computationWords n resources requests (cachedBuffers tables).value.count (originalLeafBudget tables)
  have one : 1 ≤ K := by dsimp[K,computationWords];omega
  have index (i : Fin requests) : i.val.size ≤ K :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := i.isLt;dsimp[K,computationWords];omega)
  unfold closedTrace
  dsimp only
  split
  · rename_i i returned
    constructor
    · simp only [List.length_append,List.length_cons,List.length_nil];omega
    · simpa only [wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
        or_false,forall_eq_or_imp,forall_eq,and_true] using And.intro runtime.2 (And.intro one (index i))
  · constructor
    · simp only [List.length_append,List.length_cons,List.length_nil];omega
    · simpa only [wordsWithin_append,wordsWithin_cons,wordsWithin_nil,List.mem_cons,List.not_mem_nil,
        or_false,forall_eq_or_imp,forall_eq,and_true] using And.intro runtime.2 (And.intro one (And.intro one one))

end BuyAtBulk.Computation.Runtime.Original
