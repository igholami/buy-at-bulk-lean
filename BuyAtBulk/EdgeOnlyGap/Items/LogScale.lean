import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import BuyAtBulk.EdgeOnlyGap.Items.RegularBase
import BuyAtBulk.EdgeOnlyGap.Items.Parameters
import BuyAtBulk.EdgeOnlyGap.Items.MooreBound
import BuyAtBulk.EdgeOnlyGap.Helpers.EdgeCard

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Pages 4–5: uniform quantitative logarithmic comparison and unbounded request count. Proof: handshaking gives `2·requests = n·g`; the Moore bound and `n ≤ 8g^g` give `g log g / 8 ≤ log requests ≤ 2 g log g`, from which the iterated-logarithm comparisons follow with `c = 1/8`, `C = 24`, `g₀ = 64`. -/
theorem logScale : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ g₀ : ℕ,
  ∀ (H : FiniteGraph) (g : ℕ), g₀ ≤ g → 4 ≤ g → RegularBase H g g →
    H.n ≤ 8*g^g →
    0 < Real.log (Real.log (requests H)) ∧
    c*(g:ℝ)*Real.log g ≤ Real.log (requests H) ∧
    Real.log (requests H) ≤ C*(g:ℝ)*Real.log g ∧
    c*Real.log (requests H)/Real.log (Real.log (requests H)) ≤ g ∧
    (g:ℝ) ≤ C*Real.log (requests H)/Real.log (Real.log (requests H)) ∧
    g ≤ requests H := by
  refine ⟨1/8, 24, by norm_num, by norm_num, 64, ?_⟩
  intro H g hg64 hg base hn
  classical
  -- handshaking
  have hhand : 2 * requests H = H.n * g := by
    have h := H.graph.sum_degrees_eq_twice_card_edges
    simp only [base.2.1, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at h
    unfold requests
    rw [edgeCard H]
    simpa [SimpleGraph.edgeFinset, mul_comm] using h.symm
  -- Moore
  have hmoore : (g - 1)^((g - 1)/2) ≤ H.n := mooreBound H g g hg hg base
  have hn3 : 3 ≤ H.n := le_trans (Nat.le_self_pow (by omega) _ |>.trans' (by omega)) hmoore
  have hgm : g ≤ requests H := by nlinarith
  have hm6 : 6 ≤ requests H := by nlinarith
  set m := requests H with hmdef
  have gR : (64:ℝ) ≤ g := by exact_mod_cast hg64
  have gpos : (0:ℝ) < g := by linarith
  have mR : (6:ℝ) ≤ m := by exact_mod_cast hm6
  have mpos : (0:ℝ) < m := by linarith
  have nR : (H.n:ℝ) ≤ 8 * (g:ℝ)^g := by exact_mod_cast hn
  have handR : 2 * (m:ℝ) = H.n * g := by exact_mod_cast hhand
  set ℓ := Real.log g with hℓ
  set L := Real.log m with hL
  have hlog2 := Real.log_two_gt_d9
  have hℓ1 : 1 ≤ ℓ := by
    have : Real.log 4 ≤ ℓ := Real.log_le_log (by norm_num) (by linarith)
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    linarith
  have hℓg : ℓ ≤ g := (Real.log_le_sub_one_of_pos gpos).trans (by linarith)
  -- upper bound on L
  have hmup : (m:ℝ) ≤ (g:ℝ)^(g+2) := by
    have : (m:ℝ) ≤ 4 * (g:ℝ)^g * g := by nlinarith
    calc (m:ℝ) ≤ 4 * (g:ℝ)^g * g := this
      _ ≤ g * (g:ℝ)^g * g := by gcongr; linarith
      _ = (g:ℝ)^(g+2) := by ring
  have hLup : L ≤ 2 * g * ℓ := by
    have := Real.log_le_log mpos hmup
    rw [Real.log_pow] at this
    push_cast at this
    nlinarith
  -- lower bound on L
  have hLlo : (g:ℝ) * ℓ / 8 ≤ L := by
    set r := (g - 1)/2 with hr
    have hr4 : (g:ℝ) ≤ 4 * r := by
      have : g ≤ 4 * r := by omega
      exact_mod_cast this
    have hg1 : (0:ℝ) < ((g-1:ℕ):ℝ) := by exact_mod_cast (show 0 < g - 1 by omega)
    have hsq : (g:ℝ) ≤ ((g-1:ℕ):ℝ)^2 := by
      have : g ≤ (g-1)^2 := by
        have : g ≤ (g-1)*(g-1) := by
          rcases Nat.exists_eq_add_of_le hg with ⟨k, rfl⟩
          simp only [show 4 + k - 1 = 3 + k by omega]; nlinarith
        simpa [sq] using this
      exact_mod_cast this
    have hl1 : ℓ ≤ 2 * Real.log ((g-1:ℕ):ℝ) := by
      have := Real.log_le_log gpos hsq
      rwa [Real.log_pow] at this
    have hnR : ((g-1:ℕ):ℝ)^r ≤ H.n := by exact_mod_cast hmoore
    have hlogn : (r:ℝ) * Real.log ((g-1:ℕ):ℝ) ≤ Real.log H.n := by
      have := Real.log_le_log (pow_pos hg1 r) hnR
      rwa [Real.log_pow] at this
    have hnm : (H.n:ℝ) ≤ m := by nlinarith
    have hnpos : (0:ℝ) < H.n := by exact_mod_cast (show 0 < H.n by omega)
    have := Real.log_le_log hnpos hnm
    have hl0 : 0 ≤ Real.log ((g-1:ℕ):ℝ) := by linarith
    nlinarith
  have hLg : (g:ℝ) / 8 ≤ L := by
    calc (g:ℝ)/8 ≤ g * ℓ / 8 := by nlinarith
      _ ≤ L := hLlo
  have hL1 : 1 < L := by linarith
  have hLpos : 0 < L := by linarith
  have hlogL : 0 < Real.log L := Real.log_pos hL1
  -- log L ≤ 3ℓ
  have hlogLup : Real.log L ≤ 3 * ℓ := by
    have hgg : L ≤ (g:ℝ)^3 := by
      have h1 : 2 * (g:ℝ) * ℓ ≤ 2 * g * g := by gcongr
      have h2 : 2 * (g:ℝ) * g ≤ (g:ℝ)^3 := by nlinarith
      linarith
    have := Real.log_le_log hLpos hgg
    rwa [Real.log_pow] at this
  -- ℓ ≤ 2 log L
  have hlogLlo : ℓ ≤ 2 * Real.log L := by
    have hgg : (g:ℝ) ≤ L^2 := by nlinarith
    have := Real.log_le_log gpos hgg
    rwa [Real.log_pow] at this
  refine ⟨hlogL, by linarith, by nlinarith, ?_, ?_, hgm⟩
  · rw [div_le_iff₀ hlogL]
    nlinarith
  · rw [le_div_iff₀ hlogL]
    nlinarith

end BuyAtBulk.EdgeOnlyGap
