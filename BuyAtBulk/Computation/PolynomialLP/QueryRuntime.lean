import BuyAtBulk.Computation.PolynomialLP.Words.Monotonicity
import BuyAtBulk.Computation.PolynomialLP.Words.ObjectiveSchedule

/-! Uniform actual feasibility-query costs across every bisection point.
All query arrays and their encoding bounds are derived from the stored input
and the proved dyadic grid; there is no query-cost certificate parameter. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP
open Computation Computation.Runtime Rational
variable {n m : ℕ}

theorem OnGrid.mono {U V age : ℕ} {q : ℚ} (grid : OnGrid U age q) (bound : U ≤ V) : OnGrid V age q := by
  obtain ⟨z, value, size⟩ := grid
  exact ⟨z, value, size.trans (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right bound age))⟩

namespace ObjectiveRuntime

def valueBudget (n J K : ℕ) := 2 * (4 * n + 1) * (J + K + 5) + 2

def searchDepth (n L K : ℕ) := searchRounds n (n * L) (valueBudget n (n * L) K)
def gridHeight (n L : ℕ) := n * L + n + 2

def queryWidth (n L K : ℕ) := L + 2 * (gridHeight n L + searchDepth n L K + 1) + 2

def querySize (n m L K : ℕ) := 1 + ((m + 1) + (m + 1) * n + n) * queryWidth n L K

def queryCount (n m L K : ℕ) := m * (3 * n + 13) + 5 + Trace.decisionCount n (m + 1) (querySize n m L K)

def queryWordBudget (n m L K : ℕ) := Trace.decisionWordBudget n (m + 1) (querySize n m L K) +
  m + n + queryWidth n L K + 20

theorem objectiveBits_le {input : Stored (n := n) (m := m)} {L : ℕ} (cells : CellBits input L) :
    objectiveBits input ≤ n * L := by
  simpa only [InputTrace.vectorBudget_value, objectiveBits] using
    InputTrace.vectorBudget_bound input.objective L cells.objective

@[gcongr] theorem valueBudget_mono {n n' J J' K K' : ℕ}
    (dimension : n ≤ n') (objective : J ≤ J') (coordinate : K ≤ K') :
    valueBudget n J K ≤ valueBudget n' J' K' := by dsimp only [valueBudget]; gcongr

theorem actual_search_depth {input : Stored (n := n) (m := m)} {L : ℕ}
    (cells : CellBits input L) (K : ℕ) :
    searchRounds n (objectiveBits input) (valueBits input K) ≤ searchDepth n L K := by
  have objective := objectiveBits_le cells
  have value := valueBudget_mono (le_refl n) objective (le_refl K)
  change valueBits input K ≤ valueBudget n (n * L) K at value
  dsimp only [searchDepth, searchRounds]
  omega

theorem query_cells (input : Stored (n := n) (m := m)) (L K t : ℕ) (cells : CellBits input L)
    (elapsed : t ≤ searchDepth n L K) (q : ℚ) (grid : OnGrid (gridHeight n L) t q) :
    CellBits (input.addCut input.objective q) (queryWidth n L K) := by
  have point := grid.bits
  have old : L ≤ queryWidth n L K := by dsimp only [queryWidth]; omega
  apply (cells.mono old).addCut input.objective q
  · intro j
    exact (cells.objective j).trans old
  · dsimp only [queryWidth]
    omega

theorem query_input_size (input : Stored (n := n) (m := m)) (L K t : ℕ) (cells : CellBits input L)
    (elapsed : t ≤ searchDepth n L K) (q : ℚ) (grid : OnGrid (gridHeight n L) t q) :
    inputBudget (input.addCut input.objective q) ≤ querySize n m L K :=
  (query_cells input L K t cells elapsed q grid).inputBudget

theorem below_count (input : Stored (n := n) (m := m)) (L K t : ℕ) (cells : CellBits input L)
    (elapsed : t ≤ searchDepth n L K) (q : ℚ) (grid : OnGrid (gridHeight n L) t q) :
    (belowTrace (@Trace.decideBoxed n) input q).events.length ≤ queryCount n m L K := by
  have cut := addCutTrace_count input input.objective q
  have oracle := Trace.decideBoxed_count (input.addCut input.objective q)
  have size := query_input_size input L K t cells elapsed q grid
  have uniform := Trace.decisionCount_mono (le_refl n) (le_refl (m + 1)) size
  simp only [belowTrace, Traced.bind_events, Traced.bind_value, addCutTrace_value, List.length_append]
  dsimp only [queryCount]
  omega

theorem below_words (input : Stored (n := n) (m := m)) (L K t : ℕ) (cells : CellBits input L)
    (elapsed : t ≤ searchDepth n L K) (q : ℚ) (grid : OnGrid (gridHeight n L) t q) :
    WordsWithin (queryWordBudget n m L K) (belowTrace (@Trace.decideBoxed n) input q).events := by
  let W := queryWordBudget n m L K
  have old : L ≤ W := by dsimp only [W, queryWordBudget, queryWidth]; omega
  have point := grid.bits
  have cut := addCutTrace_words input input.objective q W
    (by dsimp only [W, queryWordBudget]; omega)
    (fun i j => (cells.coefficients i j).trans old)
    (fun i => (cells.bounds i).trans old)
    (by dsimp only [W, queryWordBudget, queryWidth]; omega)
  have size := query_input_size input L K t cells elapsed q grid
  have uniform := Trace.decisionWordBudget_mono (le_refl n) (le_refl (m + 1)) size
  have oracle : WordsWithin W (Trace.decideBoxed (input.addCut input.objective q)).events :=
    (Trace.decideBoxed_words (input.addCut input.objective q)).mono
    (uniform.trans (by dsimp only [W, queryWordBudget]; omega))
  simp only [belowTrace, Traced.bind_events, Traced.bind_value, addCutTrace_value, wordsWithin_append]
  exact ⟨cut, oracle⟩

end ObjectiveRuntime
end BuyAtBulk.PolynomialLP
