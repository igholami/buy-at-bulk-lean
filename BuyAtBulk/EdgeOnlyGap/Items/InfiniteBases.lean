import BuyAtBulk.EdgeOnlyGap.Items.RegularBase
import BuyAtBulk.EdgeOnlyGap.Items.Parameters
import BuyAtBulk.EdgeOnlyGap.Items.Handshaking
import BuyAtBulk.EdgeOnlyGap.Items.ErdosSachs

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit sequence selection, pp. 1, 5: increasing girth parameter, not arbitrary h. -/
theorem infiniteBases : ∃ B : ℕ → FiniteGraph,
  (∀ k, RegularBase (B k) (k+4) (k+4) ∧ (B k).n ≤ 8*(k+4)^(k+4)) ∧
  (∀ M : ℕ, ∃ N : ℕ, ∀ k, N ≤ k → M ≤ requests (B k)) := by
  classical
  have hex (k : ℕ) := erdosSachs (k+4) (k+4) (by omega) (by omega)
  choose B hb using hex
  refine ⟨B, hb, ?_⟩
  intro M
  refine ⟨M, ?_⟩
  intro k hk
  have hbase := (hb k).1
  have hn := (B k).graph.degree_lt_card_verts (⟨0, hbase.1⟩ : Fin (B k).n)
  rw [hbase.2.1] at hn
  simp only [Fintype.card_fin] at hn
  have hs := handshaking (B k) (k+4) (k+4) hbase
  have hn2 : 2 ≤ (B k).n := by omega
  have hmul := Nat.mul_le_mul_right (k+4) hn2
  omega

end BuyAtBulk.EdgeOnlyGap
