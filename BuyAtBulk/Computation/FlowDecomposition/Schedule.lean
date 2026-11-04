import BuyAtBulk.Computation.FlowDecomposition.Algorithm
import BuyAtBulk.Computation.FlowDecomposition.SearchSchedule

/-! Instrumented extraction counts actual table-entry candidate inspections
performed by its directed searches. Other loop sizes and all rational word
sizes are established separately; this is not a total instruction counter. -/
namespace BuyAtBulk.Computation.FlowDecomposition
variable {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

def extractScheduled (source target : V) : ℕ → FlowMatrix n → ℚ →
    Option (WeightedPaths G source target) × ℕ
  | 0, matrix, mass => (extract G numbering source target 0 matrix mass, 0)
  | fuel + 1, matrix, mass =>
      if mass = 0 then (some [], 0) else
        let search := positivePathScheduled G numbering (decodedFlow numbering matrix) source target
        match search.1 with
        | none => (none, search.2)
        | some path =>
            let amount := bottleneck G (decodedFlow numbering matrix) mass path
            let recursive := extractScheduled source target fuel (subtract G numbering matrix amount path) (mass - amount)
            (recursive.1.map (fun rest => (amount, path) :: rest), search.2 + recursive.2)

theorem extractScheduled_value (source target : V) (fuel : ℕ) :
    ∀ matrix mass, (extractScheduled G numbering source target fuel matrix mass).1 = extract G numbering source target fuel matrix mass := by
  induction fuel with
  | zero => intro matrix mass; rfl
  | succ fuel ih =>
    intro matrix mass
    simp only [extractScheduled, extract, positivePathScheduled_value]
    split
    · rfl
    · cases found : positivePath G numbering (decodedFlow numbering matrix) source target with
      | none => simp only [found]
      | some path => simp only [found, ih]

theorem extractScheduled_bound (source target : V) (fuel : ℕ) :
    ∀ matrix mass, (extractScheduled G numbering source target fuel matrix mass).2 ≤ fuel * (2 * n ^ 3 + n) := by
  induction fuel with
  | zero => intro matrix mass; simp [extractScheduled]
  | succ fuel ih =>
    intro matrix mass
    have search_bound := positivePathScheduled_bound G numbering (decodedFlow numbering matrix) source target
    simp only [extractScheduled]
    split
    · dsimp only
      positivity
    · split
      · dsimp only
        nlinarith [Nat.zero_le (fuel * (2 * n ^ 3 + n))]
      · rename_i path found
        have rest := ih (subtract G numbering matrix (bottleneck G (decodedFlow numbering matrix) mass path) path)
          (mass - bottleneck G (decodedFlow numbering matrix) mass path)
        dsimp only
        nlinarith

/-- The actual decomposition's directed-search candidate visits are bounded
by a degree-five polynomial, with no dependence on denominator magnitude. -/
theorem decomposition_search_schedule (matrix : FlowMatrix n) (source target : V) :
    (extractScheduled G numbering source target (n * n + 1) matrix 1).1 = decompose G numbering matrix source target ∧
    (extractScheduled G numbering source target (n * n + 1) matrix 1).2 ≤
      (n * n + 1) * (2 * n ^ 3 + n) :=
  ⟨extractScheduled_value G numbering source target _ matrix _, extractScheduled_bound G numbering source target _ matrix _⟩

end BuyAtBulk.Computation.FlowDecomposition
