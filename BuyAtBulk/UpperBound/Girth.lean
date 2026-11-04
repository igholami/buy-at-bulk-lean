import BuyAtBulk.UpperBound.Girth.Deletion
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Positivity

namespace BuyAtBulk.UpperBound
open SimpleGraph

/-- Source `lem:girth`: an actual finite simple graph with no cycle of length
at most `2r` has at most `n(1+n^(1/r))` edges. The proof derives exploration
and low-degree deletion from graph paths; neither is a premise. -/
theorem girth_edge_bound {V : Type} [Fintype V] (G : SimpleGraph V) {r : ℕ}
    (hr : 1 ≤ r) (hg : Girth.HighGirth G r) :
    (Nat.card G.edgeSet : ℝ) ≤ (Fintype.card V : ℝ) *
      (1 + (Fintype.card V : ℝ) ^ (1 / (r : ℝ))) := by
  let x : ℝ := (Fintype.card V : ℝ) ^ ((r : ℝ)⁻¹)
  let d : ℕ := ⌊x⌋₊ + 1
  have hx : 0 ≤ x := Real.rpow_nonneg (by positivity) _
  have hxd : x < (d : ℝ) := by simpa [d] using Nat.lt_floor_add_one x
  have hpowReal : (Fintype.card V : ℝ) < (d : ℝ) ^ r := calc
    _ = x ^ r := (Real.rpow_inv_natCast_pow (by positivity) (by omega)).symm
    _ < _ := pow_lt_pow_left₀ hxd hx (by omega)
  have hpow : Fintype.card V < d ^ r := by exact_mod_cast hpowReal
  have hedges := Girth.edge_bound_integer G hr hg le_rfl hpow
  have hdle : (d : ℝ) ≤ 1 + x := by
    have := Nat.floor_le hx
    dsimp [d]
    push_cast
    linarith
  calc
    (Nat.card G.edgeSet : ℝ) ≤ (Fintype.card V : ℝ) * (d : ℝ) := by exact_mod_cast hedges
    _ ≤ (Fintype.card V : ℝ) * (1 + x) := mul_le_mul_of_nonneg_left hdle (by positivity)
    _ = _ := by simp [x, one_div]

end BuyAtBulk.UpperBound
