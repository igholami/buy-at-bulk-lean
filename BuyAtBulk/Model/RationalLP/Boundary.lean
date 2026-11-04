import BuyAtBulk.Model.RationalLP.Direction

/-! A rational improving direction reaches a new active boundary in one exact
minimum-ratio step, preserving all previously active equalities. -/
noncomputable section
namespace BuyAtBulk.RationalLP.Problem
variable {J C : Type} [Fintype J] [Fintype C] (P : Problem J C)

/-- One exact minimum-ratio step strictly increases the active constraint set. -/
theorem boundary_step (cube : P.InUnitCube) (x d : J → ℚ)
    (hx : P.Feasible x) (dne : d ≠ 0)
    (hdir : ∀ i ∈ P.active x, P.row i d = 0) (hobj : P.objective d ≤ 0) :
    ∃ y : J → ℚ, P.Feasible y ∧ P.objective y ≤ P.objective x ∧
      P.active x ⊂ P.active y := by
  classical
  let I := Finset.univ.filter fun i => 0 < P.row i d
  have Ine : I.Nonempty := by
    obtain ⟨i, hi⟩ := P.positive_row cube x d hx dne
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let ratio : C → ℚ := fun i => (P.bound i - P.row i x) / P.row i d
  obtain ⟨key, hkey, hmin⟩ := I.exists_min_image ratio Ine
  let δ := ratio key
  have inactive : ∀ i ∈ I, i ∉ P.active x := by
    intro i hi hactive
    have hp := (Finset.mem_filter.mp hi).2
    rw [hdir i hactive] at hp
    exact (lt_irrefl 0) hp
  have slack_pos : ∀ i ∈ I, 0 < P.bound i - P.row i x := by
    intro i hi
    have hneq : P.row i x ≠ P.bound i := by simpa [active] using inactive i hi
    exact sub_pos.mpr (lt_of_le_of_ne (hx i) hneq)
  have δpos : 0 < δ := div_pos (slack_pos key hkey) (Finset.mem_filter.mp hkey).2
  let y := x + δ • d
  have row_y : ∀ i, P.row i y = P.row i x + δ * P.row i d := by
    intro i; simp [y, map_add, map_smul]
  have hy : P.Feasible y := by
    intro i
    rw [row_y]
    by_cases hi : i ∈ I
    · have hδ : δ * P.row i d ≤ P.bound i - P.row i x :=
        (le_div_iff₀ (Finset.mem_filter.mp hi).2).mp (hmin i hi)
      linarith
    · have hd : P.row i d ≤ 0 := by simpa [I] using hi
      have hprod := mul_nonpos_of_nonneg_of_nonpos (le_of_lt δpos) hd
      have hix := hx i
      linarith
  have subset : P.active x ⊆ P.active y := by
    intro i hi
    have hix := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [row_y, hdir i hi, mul_zero, add_zero]
    exact hix
  have keyactive : key ∈ P.active y := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [row_y]
    have hder : P.row key d ≠ 0 := ne_of_gt (Finset.mem_filter.mp hkey).2
    dsimp [δ, ratio]
    field_simp
    ring
  refine ⟨y, hy, ?_, Finset.ssubset_iff_subset_ne.mpr ⟨subset, ?_⟩⟩
  · have hprod := mul_nonpos_of_nonneg_of_nonpos (le_of_lt δpos) hobj
    simp only [y, map_add, map_smul, smul_eq_mul]
    linarith
  · intro heq
    rw [← heq] at keyactive
    exact inactive key hkey keyactive

end BuyAtBulk.RationalLP.Problem
