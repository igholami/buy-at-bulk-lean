import BuyAtBulk.EdgeOnlyGap.Items.PositiveModification
import BuyAtBulk.EdgeOnlyGap.Items.PrivateLeaves
import BuyAtBulk.EdgeOnlyGap.Items.CoefficientBits
import BuyAtBulk.EdgeOnlyGap.Items.RegularBase
import BuyAtBulk.EdgeOnlyGap.Items.CoreResource
import BuyAtBulk.EdgeOnlyGap.Items.MooreBound
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofCCoefficientBits
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofCCoreCrossing

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit coefficient classification and bit estimate, p. 5. -/
theorem finalCoefficientData (H : FiniteGraph) (q g : ℕ) (π : Lift H q)
    (hg : 4 ≤ g) (base : RegularBase H g g) :
  let D := privateLeaves (positiveData H q g π (by omega))
    (1/(10*(requests H:ℚ))) (by positivity)
  (∀ a, D.buying a ∈ ({1,1/(requests H:ℚ),1/(10*(requests H:ℚ))} : Finset ℚ) ∧
    D.length a ∈ ({2/(g:ℚ),1/(requests H:ℚ),1/(10*(requests H:ℚ))} : Finset ℚ)) ∧
  CoefficientsBounded D 32 := by
  intro D
  have hm := proofC_requestsHandshake H g g base
  have hn := base.1
  have hmoore := mooreBound H g g hg hg base
  have hn3 : 3 ≤ H.n := le_trans (Nat.le_self_pow (by omega) _ |>.trans' (by omega)) hmoore
  have hgm : g ≤ requests H := by nlinarith
  have hm0 : 0 < requests H := by omega
  have hclass : ∀ a, D.buying a ∈ ({1,1/(requests H:ℚ),1/(10*(requests H:ℚ))} : Finset ℚ) ∧
      D.length a ∈ ({2/(g:ℚ),1/(requests H:ℚ),1/(10*(requests H:ℚ))} : Finset ℚ) := by
    intro a
    simp only [D, privateLeaves]
    split
    · rename_i j _
      simp only [positiveData, coreResource, supplyData, Sum.inr.injEq]
      split_ifs <;> simp
    · simp
  refine ⟨hclass, fun a => ?_⟩
  have hreq : D.requestCount = requests H := rfl
  rw [hreq]
  have hsz := proofC_size_mul_ten (requests H)
  have hgs := Nat.size_le_size hgm
  have h2 : (2:ℕ).size ≤ 2 := by decide
  have h1 : (1:ℕ).size ≤ 1 := by decide
  have bound : ∀ x ∈ ({1, 1/(requests H:ℚ), 1/(10*(requests H:ℚ)), 2/(g:ℚ)} : Finset ℚ),
      coefficientBits x ≤ 32 * ((requests H).size + 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have := proofC_bits_div 1 1 one_pos
      norm_num at this ⊢
      omega
    · have := proofC_bits_div 1 (requests H) hm0
      norm_num at this ⊢
      omega
    · have := proofC_bits_div 1 (10 * requests H) (by omega)
      push_cast at this
      norm_num at this ⊢
      omega
    · have := proofC_bits_div 2 g (by omega)
      push_cast at this
      omega
  obtain ⟨hb, hl⟩ := hclass a
  constructor
  · apply bound
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb ⊢
    rcases hb with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · apply bound
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl ⊢
    rcases hl with h | h | h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))

end BuyAtBulk.EdgeOnlyGap
