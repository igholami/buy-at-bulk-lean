import BuyAtBulk.EdgeOnlyGap.Items.BuyingDetour
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 4: coefficient bound and elementary cost minimization. -/
theorem smallRoutingBound (n h d g S L : ℕ) (hd : 0 < d) (hg : 4 ≤ g)
    (handshake : 2*h=n*d)
    (budget : (h : ℚ) ≤ S + (1/((g:ℚ)-1)+2/(g:ℚ))*L) :
  1/((g:ℚ)-1)+2/(g:ℚ) ≤ 4/(g:ℚ) ∧
  (S : ℚ)+2*L/(d:ℚ) ≥ min (h:ℚ) ((h:ℚ)*g/(2*d)) ∧
  min (h:ℚ) ((h:ℚ)*g/(2*d)) = (n:ℚ)*min ((d:ℚ)/2) ((g:ℚ)/4) := by
  have hg_rat : (4 : ℚ) ≤ (g : ℚ) := by exact_mod_cast hg
  have hg_pos : (0 : ℚ) < (g : ℚ) := by linarith
  have hg1_pos : (0 : ℚ) < (g : ℚ) - 1 := by linarith
  have hd_pos : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  have hL_nonneg : (0 : ℚ) ≤ (L : ℚ) := Nat.cast_nonneg L
  have hS_nonneg : (0 : ℚ) ≤ (S : ℚ) := Nat.cast_nonneg S
  have hn_nonneg : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
  have hcoeff : 1 / ((g : ℚ) - 1) + 2 / (g : ℚ) ≤ 4 / (g : ℚ) := by
    rw [div_add_div _ _ (ne_of_gt hg1_pos) (ne_of_gt hg_pos)]
    rw [div_le_div_iff₀ (mul_pos hg1_pos hg_pos) hg_pos]
    nlinarith
  have hbudget' : (h : ℚ) ≤ (S : ℚ) + (4 / (g : ℚ)) * (L : ℚ) := by
    calc (h : ℚ)
      _ ≤ (S : ℚ) + (1 / ((g : ℚ) - 1) + 2 / (g : ℚ)) * (L : ℚ) := budget
      _ ≤ (S : ℚ) + (4 / (g : ℚ)) * (L : ℚ) := by gcongr
  refine ⟨hcoeff, ?_, ?_⟩
  · by_cases hgd : (g : ℚ) ≤ 2 * (d : ℚ)
    · have hfactor : (g : ℚ) / (2 * (d : ℚ)) ≤ 1 := by
        rw [div_le_iff₀ (by positivity)]
        simpa using hgd
      have hm := mul_le_mul_of_nonneg_right hbudget'
        (show (0 : ℚ) ≤ (g : ℚ) / (2 * (d : ℚ)) by positivity)
      have hid : ((S : ℚ) + 4 / (g : ℚ) * L) * ((g : ℚ) / (2 * (d : ℚ))) =
          (S : ℚ) * ((g : ℚ) / (2 * (d : ℚ))) + 2 * L / d := by
        field_simp [ne_of_gt hg_pos, ne_of_gt hd_pos]
        <;> ring
      rw [hid] at hm
      have hS := mul_le_mul_of_nonneg_left hfactor hS_nonneg
      have hmin := min_le_right (h : ℚ) ((h : ℚ) * g / (2 * d))
      change _ ≤ _
      nlinarith [show (h : ℚ) * ((g : ℚ) / (2 * (d : ℚ))) =
        (h : ℚ) * g / (2 * d) by ring]
    · have hcoeff' : 4 / (g : ℚ) ≤ 2 / (d : ℚ) := by
        rw [div_le_div_iff₀ hg_pos hd_pos]
        linarith
      have hm := mul_le_mul_of_nonneg_right hcoeff' hL_nonneg
      have hmin := min_le_left (h : ℚ) ((h : ℚ) * g / (2 * d))
      nlinarith [show (2 / (d : ℚ)) * L = 2 * (L : ℚ) / d by ring]
  · have hhs : 2 * (h : ℚ) = (n : ℚ) * (d : ℚ) := by exact_mod_cast handshake
    have hh : (h : ℚ) = (n : ℚ) * ((d : ℚ) / 2) := by linarith
    have hhg : (h : ℚ) * (g : ℚ) / (2 * (d : ℚ)) = (n : ℚ) * ((g : ℚ) / 4) := by
      field_simp [ne_of_gt hd_pos]
      linarith
    rw [hhg, hh, ← mul_min_of_nonneg _ _ hn_nonneg]

end BuyAtBulk.EdgeOnlyGap
