import BuyAtBulk.Computation.FlowDecomposition.Algorithm

namespace BuyAtBulk.Computation.FlowDecomposition
open BuyAtBulk.CompactFlow
variable {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

/-- The executable extraction returns positive weights, exact remaining mass
and an arcwise dominated sparse path list. Strict support descent pays for fuel. -/
theorem extract_correct (source target : V) (fuel : ℕ) :
    ∀ (matrix : FlowMatrix n) (mass : ℚ),
      (positiveArcs (decodedFlow numbering matrix)).card < fuel → 0 ≤ mass →
      (∀ u v, 0 ≤ decodedFlow numbering matrix u v) →
      (∀ u v, ¬G.Adj u v → decodedFlow numbering matrix u v = 0) →
      (∀ v, (∑ u, decodedFlow numbering matrix v u) - (∑ u, decodedFlow numbering matrix u v) =
        mass * ((if source = v then 1 else 0) - (if target = v then 1 else 0))) →
      ∃ entries : WeightedPaths G source target,
        extract G numbering source target fuel matrix mass = some entries ∧
        (∀ entry ∈ entries, 0 < entry.1) ∧
        (entries.map Prod.fst).sum = mass ∧
        (∀ u v, (entries.map fun entry => entry.1 * transportVisits entry.2.val u v).sum ≤ decodedFlow numbering matrix u v) ∧
        entries.length ≤ fuel := by
  induction fuel with
  | zero => intro matrix mass impossible; omega
  | succ fuel ih =>
    intro matrix mass support mass_nonneg nonneg nonedge balance
    by_cases zero : mass = 0
    · refine ⟨[], by simp [extract, zero], by simp, by simp [zero], ?_, by simp⟩
      intro u v
      simpa using nonneg u v
    have mass_pos : 0 < mass := lt_of_le_of_ne mass_nonneg (Ne.symm zero)
    obtain ⟨path, found⟩ := positivePath_exists G numbering (decodedFlow numbering matrix) source target mass mass_pos nonneg nonedge balance
    have positive := positivePath_some G numbering (decodedFlow numbering matrix) source target path found
    let amount := bottleneck G (decodedFlow numbering matrix) mass path
    obtain ⟨amount_pos, amount_mass, residual_nonneg, strict⟩ :=
      bottleneck_spec G path (decodedFlow numbering matrix) positive nonneg mass mass_pos
    let residual := subtract G numbering matrix amount path
    have residualFlow : decodedFlow numbering residual = fun u v => decodedFlow numbering matrix u v - amount * transportVisits path.val u v := by
      funext u v
      exact subtract_flow G numbering matrix amount path u v
    have residual_nonedge : ∀ u v, ¬G.Adj u v → decodedFlow numbering residual u v = 0 := by
      intro u v missing
      rw [residualFlow]
      change decodedFlow numbering matrix u v - amount * transportVisits path.val u v = 0
      rw [nonedge u v missing, transportVisits_nonedge _ u v missing, mul_zero, sub_zero]
    have residual_balance : ∀ v, (∑ u, decodedFlow numbering residual v u) - (∑ u, decodedFlow numbering residual u v) =
        (mass - amount) * ((if source = v then 1 else 0) - (if target = v then 1 else 0)) := by
      have model := subtract_path_balance path (decodedFlow numbering matrix) mass amount (by
        intro v
        by_cases hs : source = v <;> by_cases ht : target = v <;> simpa [hs, ht] using balance v)
      intro v
      rw [residualFlow]
      by_cases hs : source = v <;> by_cases ht : target = v <;> simpa [hs, ht] using model v
    have remainder : ∃ rest : WeightedPaths G source target,
        extract G numbering source target fuel residual (mass - amount) = some rest ∧
        (∀ entry ∈ rest, 0 < entry.1) ∧ (rest.map Prod.fst).sum = mass - amount ∧
        (∀ u v, (rest.map fun entry => entry.1 * transportVisits entry.2.val u v).sum ≤ decodedFlow numbering residual u v) ∧
        rest.length ≤ fuel := by
      by_cases exhausted : amount = mass
      · refine ⟨[], ?_, by simp, by simp [exhausted], ?_, by simp⟩
        · rw [exhausted, sub_self]
          exact extract_zero G numbering source target fuel residual
        · intro u v
          rw [residualFlow]
          simpa [amount] using residual_nonneg u v
      · have amount_lt : amount < mass := lt_of_le_of_ne amount_mass exhausted
        have support_smaller : (positiveArcs (decodedFlow numbering residual)).card < fuel := by
          rw [residualFlow]
          have smaller : (positiveArcs (fun u v => decodedFlow numbering matrix u v - amount * transportVisits path.val u v)).card <
              (positiveArcs (decodedFlow numbering matrix)).card := strict amount_lt
          omega
        apply ih residual (mass - amount) support_smaller (sub_nonneg.mpr amount_mass)
        · intro u v
          rw [residualFlow]
          exact residual_nonneg u v
        · exact residual_nonedge
        · exact residual_balance
    obtain ⟨rest, returned, positive_rest, mass_rest, cap_rest, length_rest⟩ := remainder
    refine ⟨(amount, path) :: rest, ?_, ?_, ?_, ?_, by simpa using Nat.succ_le_succ length_rest⟩
    · simp only [extract, if_neg zero, found]
      change Option.map _ (extract G numbering source target fuel residual (mass - amount)) = _
      rw [returned]
      rfl
    · intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact amount_pos
      · exact positive_rest entry member
    · simp only [List.map_cons, List.sum_cons, Prod.fst]
      linarith
    · intro u v
      simp only [List.map_cons, List.sum_cons]
      have cap := cap_rest u v
      rw [residualFlow] at cap
      linarith

/-- Unit transport flow yields at most n²+1 actual weighted simple paths,
with exact unit mass and no increased directed arc use. -/
theorem decompose_correct (matrix : FlowMatrix n) (source target : V)
    (nonneg : ∀ u v, 0 ≤ decodedFlow numbering matrix u v)
    (nonedge : ∀ u v, ¬G.Adj u v → decodedFlow numbering matrix u v = 0)
    (balance : ∀ v, (∑ u, decodedFlow numbering matrix v u) - (∑ u, decodedFlow numbering matrix u v) =
      (if source = v then 1 else 0) - (if target = v then 1 else 0)) :
    ∃ entries : WeightedPaths G source target,
      decompose G numbering matrix source target = some entries ∧
      (∀ entry ∈ entries, 0 < entry.1) ∧ (entries.map Prod.fst).sum = 1 ∧
      (∀ u v, (entries.map fun entry => entry.1 * transportVisits entry.2.val u v).sum ≤ decodedFlow numbering matrix u v) ∧
      entries.length ≤ n * n + 1 := by
  apply extract_correct G numbering source target (n * n + 1) matrix 1
  · have bound := Finset.card_le_univ (positiveArcs (decodedFlow numbering matrix))
    simp only [Fintype.card_prod, numbered_card numbering] at bound
    omega
  · norm_num
  · exact nonneg
  · exact nonedge
  · simpa only [one_mul] using balance

end BuyAtBulk.Computation.FlowDecomposition
