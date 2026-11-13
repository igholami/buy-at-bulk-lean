import BuyAtBulk.EdgeOnlyGap.Items.RegularBase
import BuyAtBulk.EdgeOnlyGap.Helpers.ErdosSachsMaximal

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Erdős–Sachs theorem, in the weak form used by the note (p. 1): for `d, g ≥ 4` there is a
nonempty `d`-regular graph of girth at least `g` on at most `8·d^g` vertices. Reference:
P. Erdős and H. Sachs, “Reguläre Graphen gegebener Taillenweite mit minimaler Knotenzahl”,
Wiss. Z. Martin-Luther-Univ. Halle-Wittenberg, Math.-Natur. Reihe 12 (1963), 251–258.

Proof: an edge-maximal graph on `2·d^g` vertices with maximum degree `d` and girth `g` is
`d`-regular (`ErdosSachs.exists_regular_girth`). -/
theorem erdosSachs (d g : ℕ) (hd : 4 ≤ d) (hg : 4 ≤ g) :
    ∃ H : FiniteGraph, RegularBase H d g ∧ H.n ≤ 8 * d^g := by
  obtain ⟨G, hdeg, hcyc⟩ := ErdosSachs.exists_regular_girth d g hd hg
  refine ⟨⟨2 * d ^ g, G⟩, ⟨?_, fun v => ?_, ?_⟩, ?_⟩
  · have : 0 < d ^ g := pow_pos (by omega) g
    change 0 < 2 * d ^ g
    omega
  · convert hdeg v
  · change ((g : ℕ) : ℕ∞) ≤ G.egirth
    rw [SimpleGraph.le_egirth]
    intro a w hw
    exact_mod_cast hcyc a w hw
  · change 2 * d ^ g ≤ 8 * d ^ g
    omega

end BuyAtBulk.EdgeOnlyGap
