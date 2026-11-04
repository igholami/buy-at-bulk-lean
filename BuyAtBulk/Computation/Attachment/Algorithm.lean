import BuyAtBulk.Computation.Attachment.CenterSearch

/-! Deterministic executable Algorithm ConnectEndpoint. Every metric query is
computed by bounded Bellman–Ford; center ties use the stored record order. -/
namespace BuyAtBulk.Computation.Attachment
open BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

def run (buying physical : V → ℚ) (allowance cutoff ratio threshold : ℚ) (s t : V) :
    (fuel : ℕ) → (scale : ℚ) → (z u : V) → G.Path z u → RoundingState G →
      RoundingState G × AttachmentOutcome G s t z u
  | 0, _, _, _, inherited, state => (purchase G state inherited, .arm inherited)
  | fuel + 1, scale, z, u, inherited, state =>
    if scale ≤ cutoff then (purchase G state inherited, .arm inherited) else
      let weight := mixedWeight G buying physical state allowance scale
      match shortRoute G numbering weight s t (scale / 16) with
      | some route => (purchase G state route, .completed route)
      | none =>
        match nearRecord G numbering weight scale z state.centers with
        | none =>
          (recordEdge G (purchase G (recordBirth G state z scale) inherited) inherited scale, .arm inherited)
        | some ⟨v, near⟩ =>
          match boughtRoute G numbering physical state u v threshold with
          | none =>
            (recordEdge G (purchase G (purchase G state inherited) near)
              (inherited.val.reverse.append near.val).toPath scale, .arm inherited)
          | some bypass =>
            let recursive := run buying physical allowance cutoff ratio threshold s t fuel
              (scale / ratio) z v near state
            match recursive.2 with
            | .arm returned => (recursive.1, .arm (returned.val.append bypass.reverse.val).toPath)
            | .completed completed => (recursive.1, .completed completed)

end BuyAtBulk.Computation.Attachment
