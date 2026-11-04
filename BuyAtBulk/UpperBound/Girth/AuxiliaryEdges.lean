import BuyAtBulk.UpperBound.Girth

namespace BuyAtBulk.UpperBound
open SimpleGraph

/-- Source `cor:aux-edges`: the birth-count and request-count vertex bounds,
together with the actual girth conclusion, give the required auxiliary edge
count. The algorithm must separately establish the two vertex bounds and girth. -/
theorem auxiliary_edge_count {V : Type} [Fintype V] (G : SimpleGraph V)
    {r h N : ℕ} (hr : 1 ≤ r) (hg : Girth.HighGirth G r)
    (hrequests : Fintype.card V ≤ 2 * h) (hbirths : Fintype.card V ≤ N) :
    (Nat.card G.edgeSet : ℝ) ≤
      (1 + (2 * (h : ℝ)) ^ (1 / (r : ℝ))) * (N : ℝ) := by
  have hvertex : (Fintype.card V : ℝ) ≤ 2 * (h : ℝ) := by exact_mod_cast hrequests
  have hroot : (Fintype.card V : ℝ) ^ (1 / (r : ℝ)) ≤
      (2 * (h : ℝ)) ^ (1 / (r : ℝ)) :=
    Real.rpow_le_rpow (by positivity) hvertex (by positivity)
  have hbirth : (Fintype.card V : ℝ) ≤ N := by exact_mod_cast hbirths
  calc
    (Nat.card G.edgeSet : ℝ) ≤ (Fintype.card V : ℝ) *
      (1 + (Fintype.card V : ℝ) ^ (1 / (r : ℝ))) := girth_edge_bound G hr hg
    _ ≤ (Fintype.card V : ℝ) * (1 + (2 * (h : ℝ)) ^ (1 / (r : ℝ))) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ (N : ℝ) * (1 + (2 * (h : ℝ)) ^ (1 / (r : ℝ))) :=
      mul_le_mul_of_nonneg_right hbirth (by positivity)
    _ = _ := mul_comm _ _

end BuyAtBulk.UpperBound
