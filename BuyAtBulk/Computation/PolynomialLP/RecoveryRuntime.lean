import BuyAtBulk.Computation.PolynomialLP.QueryRuntime

/-! The complete objective-value recovery program uses the actual unconditional
feasibility implementation. Every query, bracket word and reconstruction stage
has a fixed polynomial bound from stored cell lengths and original vertex bits. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace BuyAtBulk.PolynomialLP.ObjectiveRuntime
open Computation Computation.Runtime Rational
variable {n m : ℕ}

def scheduleCount (n L K : ℕ) := n * (6 * L + 17) + 1 + 2 * (n * L + n + 2) +
  2 * (valueBudget n (n * L) K + 1) + 24

def reconstructionSize (n L K : ℕ) := 2 * (n * L + n + searchDepth n L K + 3) + 3

def reconstructionCount (n L K : ℕ) :=
  let R := reconstructionSize n L K
  (2 * R + 1) * (44 * R + 23) + 6 * R + 8

def reconstructionWordBudget (n L K : ℕ) :=
  let R := reconstructionSize n L K
  ReconstructionRuntime.wordBudget (2 * R) R + valueBudget n (n * L) K + 10

def recoverCount (n m L K : ℕ) := scheduleCount n L K +
  searchDepth n L K * (queryCount n m L K + 9) + reconstructionCount n L K

def recoverWordBudget (n m L K : ℕ) := scheduleWordBudget n (n * L) K + queryWordBudget n m L K +
  64 * (gridHeight n L + searchDepth n L K + 2) + 256 + reconstructionWordBudget n L K + n + m + 20

def recoverActual (input : Stored (n := n) (m := m)) (K : ℕ) : Traced (Option ℚ) :=
  recover (@Trace.decideBoxed n) input K

@[simp] theorem recoverActual_value (input : Stored (n := n) (m := m)) (K : ℕ) :
    (recoverActual input K).value = recoverValue input K :=
  recover_value (@Trace.decideBoxed n) (fun input => Trace.decideBoxed_value input) input K

theorem schedule_count_uniform (input : Stored (n := n) (m := m)) (L K : ℕ) (cells : CellBits input L) :
    (schedule input K).events.length ≤ scheduleCount n L K := by
  have actual := schedule_count input K
  have vector := InputTrace.vectorBudget_count input.objective L cells.objective
  have objective := objectiveBits_le cells
  have value := valueBudget_mono (le_refl n) objective (le_refl K)
  change valueBits input K ≤ valueBudget n (n * L) K at value
  dsimp only [scheduleCount]
  omega

theorem search_trace_bits (input : Stored (n := n) (m := m)) (L K : ℕ) (cells : CellBits input L) :
    let result := (bisectTrace (belowTrace (@Trace.decideBoxed n) input)
      (searchRounds n (objectiveBits input) (valueBits input K)) (searchBracket n (objectiveBits input))).value
    (Code.ofRat result.lower).bits + 1 ≤ reconstructionSize n L K ∧
      (Code.ofRat result.upper).bits + 1 ≤ reconstructionSize n L K := by
  have native := bisect_search_bits (fun q => (belowTrace (@Trace.decideBoxed n) input q).value)
    (searchRounds n (objectiveBits input) (valueBits input K)) n (objectiveBits input)
  have objective := objectiveBits_le cells
  have depth := actual_search_depth cells K
  dsimp only
  rw [bisectTrace_value]
  dsimp only [reconstructionSize]
  constructor <;> omega

theorem recoverActual_count (input : Stored (n := n) (m := m)) (L K : ℕ) (cells : CellBits input L) :
    (recoverActual input K).events.length ≤ recoverCount n m L K := by
  let T := searchRounds n (objectiveBits input) (valueBits input K)
  let result := bisectTrace (belowTrace (@Trace.decideBoxed n) input) T (searchBracket n (objectiveBits input))
  let D := 2 ^ (valueBits input K + 1)
  let R := reconstructionSize n L K
  have objective := objectiveBits_le cells
  have depth := actual_search_depth cells K
  have initial := searchBracket_grid n (objectiveBits input)
  have height : objectiveBits input + n + 2 ≤ gridHeight n L := by dsimp only [gridHeight]; omega
  have binary := bisectTrace_count (belowTrace (@Trace.decideBoxed n) input) T (gridHeight n L) 0
    (queryCount n m L K) _ (initial.1.mono height) (initial.2.mono height)
    (by intro t elapsed q grid; exact below_count input L K t cells (by dsimp only [T] at elapsed; omega) q grid)
  have binaryBound : result.events.length ≤ searchDepth n L K * (queryCount n m L K + 9) :=
    binary.trans (Nat.mul_le_mul_right _ depth)
  have endpoint := search_trace_bits input L K cells
  have lowerCode := Code.bounded_mono (Code.bounded_of_bits (Code.ofRat result.value.lower)) endpoint.1
  have upperCode : (Code.ofRat result.value.upper).bits ≤ 2 * R + 2 := by
    have bound := endpoint.2
    change (Code.ofRat result.value.upper).bits + 1 ≤ R at bound
    omega
  have reconstruction := (ReconstructionRuntime.reconstructComplete_runtime result.value.lower result.value.upper D R lowerCode upperCode).2.1
  have preparation := schedule_count_uniform input L K cells
  simp only [recoverActual, recover, Traced.bind_events, Traced.bind_value,
    schedule_value, List.length_append]
  change (schedule input K).events.length + (result.events.length +
    (ReconstructionRuntime.reconstructComplete result.value.lower result.value.upper D).events.length) ≤ _
  dsimp only [recoverCount, reconstructionCount]
  dsimp only [R] at reconstruction
  omega

theorem recoverActual_words (input : Stored (n := n) (m := m)) (L K : ℕ) (cells : CellBits input L) :
    WordsWithin (recoverWordBudget n m L K) (recoverActual input K).events := by
  let W := recoverWordBudget n m L K
  let T := searchRounds n (objectiveBits input) (valueBits input K)
  let result := bisectTrace (belowTrace (@Trace.decideBoxed n) input) T (searchBracket n (objectiveBits input))
  let D := 2 ^ (valueBits input K + 1)
  let R := reconstructionSize n L K
  have objective := objectiveBits_le cells
  have depth := actual_search_depth cells K
  have value := valueBudget_mono (le_refl n) objective (le_refl K)
  change valueBits input K ≤ valueBudget n (n * L) K at value
  have preparation := (schedule_words input K).mono
    ((scheduleWordBudget_mono (le_refl n) objective (le_refl K)).trans
      (show _ ≤ W by dsimp only [W, recoverWordBudget]; omega))
  have initial := searchBracket_grid n (objectiveBits input)
  have height : objectiveBits input + n + 2 ≤ gridHeight n L := by dsimp only [gridHeight]; omega
  have binary := bisectTrace_words (belowTrace (@Trace.decideBoxed n) input) T (gridHeight n L) 0 W _
    (initial.1.mono height) (initial.2.mono height)
    (by dsimp only [T, W, recoverWordBudget]; omega)
    (by
      intro t elapsed q grid
      exact (below_words input L K t cells (by dsimp only [T] at elapsed; omega) q grid).mono
        (show _ ≤ W by dsimp only [W, recoverWordBudget]; omega))
  have endpoint := search_trace_bits input L K cells
  have lowerCode := Code.bounded_mono (Code.bounded_of_bits (Code.ofRat result.value.lower)) endpoint.1
  have upperCode : (Code.ofRat result.value.upper).bits ≤ 2 * R + 2 := by
    have bound := endpoint.2
    change (Code.ofRat result.value.upper).bits + 1 ≤ R at bound
    omega
  have reconstruction := ReconstructionRuntime.reconstructComplete_words result.value.lower result.value.upper D R lowerCode upperCode
  have denominator : D.size = valueBits input K + 2 := by simp [D, Nat.size_pow]
  have reconstructionBound : WordsWithin W
      (ReconstructionRuntime.reconstructComplete result.value.lower result.value.upper D).events :=
    reconstruction.mono (by rw [denominator]; dsimp only [W, recoverWordBudget, reconstructionWordBudget]; dsimp only [R]; omega)
  simp only [recoverActual, recover, Traced.bind_events, Traced.bind_value,
    schedule_value, wordsWithin_append]
  exact ⟨preparation, binary, reconstructionBound⟩

theorem recoverActual_runtime (input : Stored (n := n) (m := m)) (L K : ℕ) (cells : CellBits input L) :
    (recoverActual input K).value = recoverValue input K ∧
    (recoverActual input K).events.length ≤ recoverCount n m L K ∧
    WordsWithin (recoverWordBudget n m L K) (recoverActual input K).events :=
  ⟨recoverActual_value input K, recoverActual_count input L K cells, recoverActual_words input L K cells⟩

end BuyAtBulk.PolynomialLP.ObjectiveRuntime
