import BuyAtBulk.Computation.Serve

/-! Executable batch iteration over supplied original request indices. Every
returned route retains its request index, including repeated requests. -/
namespace BuyAtBulk.Computation.Batch
open BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

abbrev RouteEntry {h : ℕ} (source target : Fin h → V) := Σ i : Fin h, G.Path (source i) (target i)

def run {h : ℕ} (buying physical : V → ℚ) (budget : ℚ) (ratio : ℕ) (thresholdFactor : ℚ)
    (source target : Fin h → V) (allowance : Fin h → ℚ) :
    List (Fin h) → RoundingState G → Option (RoundingState G × List (RouteEntry G source target))
  | [], before => some (before, [])
  | i :: rest, before =>
    match Serve.run G numbering buying physical budget (allowance i) h ratio (thresholdFactor * allowance i)
        (source i) (target i) before with
    | none => none
    | some (middle, route) =>
      match run buying physical budget ratio thresholdFactor source target allowance rest middle with
      | none => none
      | some (after, entries) => some (after, ⟨i, route⟩ :: entries)

end BuyAtBulk.Computation.Batch
