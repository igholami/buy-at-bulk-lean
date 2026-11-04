import BuyAtBulk.Computation.FlowDecomposition.Bottleneck

/-! Actual support-bounded rational flow extraction. Residual tables are
materialized vectors, and paths are chosen by the directed finite search. -/
namespace BuyAtBulk.Computation.FlowDecomposition
variable {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

abbrev WeightedPaths (source target : V) := List (ℚ × G.Path source target)

def extract (source target : V) : ℕ → FlowMatrix n → ℚ → Option (WeightedPaths G source target)
  | 0, _, mass => if mass = 0 then some [] else none
  | fuel + 1, matrix, mass =>
      if mass = 0 then some [] else
        match positivePath G numbering (decodedFlow numbering matrix) source target with
        | none => none
        | some path =>
            let amount := bottleneck G (decodedFlow numbering matrix) mass path
            (extract source target fuel (subtract G numbering matrix amount path) (mass - amount)).map
              fun rest => (amount, path) :: rest

def decompose (matrix : FlowMatrix n) (source target : V) : Option (WeightedPaths G source target) :=
  extract G numbering source target (n * n + 1) matrix 1

@[simp] theorem extract_zero (source target : V) (fuel : ℕ) (matrix : FlowMatrix n) :
    extract G numbering source target fuel matrix 0 = some [] := by
  cases fuel <;> simp [extract]

end BuyAtBulk.Computation.FlowDecomposition
