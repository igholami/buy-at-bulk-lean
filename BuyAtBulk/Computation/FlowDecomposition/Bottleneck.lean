import BuyAtBulk.Computation.FlowDecomposition.SearchCorrectness
import BuyAtBulk.Model.CompactFlowBottleneck

namespace BuyAtBulk.Computation.FlowDecomposition
open BuyAtBulk.CompactFlow
variable {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

def usesArc {source target : V} (path : G.Path source target) (u v : V) : Bool :=
  path.val.darts.any fun dart => decide (dart.fst = u ∧ dart.snd = v)

theorem usesArc_iff {source target : V} (path : G.Path source target) (u v : V) :
    usesArc G path u v = true ↔ ∃ dart ∈ path.val.darts, dart.fst = u ∧ dart.snd = v := by
  simp [usesArc, List.any_eq_true]

theorem visits_eq_usesArc {source target : V} (path : G.Path source target) (u v : V) :
    transportVisits path.val u v = if usesArc G path u v then 1 else 0 := by
  by_cases edge : G.Adj u v
  · let dart : G.Dart := ⟨(u, v), edge⟩
    have indicator := path_transportVisits_dart path dart
    have same : dart ∈ path.val.darts ↔ usesArc G path u v = true := by
      rw [usesArc_iff]
      constructor
      · intro member
        exact ⟨dart, member, rfl, rfl⟩
      · rintro ⟨other, member, fst, snd⟩
        have equal : other = dart := by
          apply SimpleGraph.Dart.ext
          exact Prod.ext fst snd
        exact equal ▸ member
    change transportVisits path.val u v = _ at indicator
    simpa only [same] using indicator
  · rw [transportVisits_nonedge _ u v edge]
    have unused : usesArc G path u v = false := by
      apply Bool.eq_false_iff.mpr
      intro used
      obtain ⟨dart, _, fst, snd⟩ := (usesArc_iff G path u v).mp used
      exact edge (by simpa only [fst, snd] using dart.adj)
    simp [unused]

def bottleneck {source target : V} (flow : V → V → ℚ) (mass : ℚ)
    (path : G.Path source target) : ℚ :=
  let values := insert mass (path.val.darts.map fun dart => flow dart.fst dart.snd).toFinset
  values.min' ⟨mass, Finset.mem_insert_self _ _⟩

abbrev FlowMatrix (n : ℕ) := Vector (Vector ℚ n) n

def matrixFlow (matrix : FlowMatrix n) (u v : Fin n) : ℚ := matrix[u.val][v.val]

def decodedFlow (numbering : V ≃ Fin n) (matrix : FlowMatrix n) (u v : V) : ℚ :=
  matrixFlow matrix (numbering u) (numbering v)

def subtract {source target : V} (matrix : FlowMatrix n) (amount : ℚ)
    (path : G.Path source target) : FlowMatrix n :=
  Vector.ofFn fun u => Vector.ofFn fun v => matrixFlow matrix u v -
    if usesArc G path (numbering.symm u) (numbering.symm v) then amount else 0

@[simp] theorem subtract_flow {source target : V} (matrix : FlowMatrix n) (amount : ℚ)
    (path : G.Path source target) (u v : V) :
    decodedFlow numbering (subtract G numbering matrix amount path) u v =
      decodedFlow numbering matrix u v - amount * transportVisits path.val u v := by
  simp only [subtract, decodedFlow, matrixFlow, Vector.getElem_ofFn, Equiv.symm_apply_apply]
  rw [visits_eq_usesArc]
  split <;> simp_all

/-- The actual finite minimum is positive and removes an arc whenever it does
not exhaust the remaining mass. No existential bottleneck is selected. -/
theorem bottleneck_spec {source target : V} (path : G.Path source target)
    (flow : V → V → ℚ) (positive : PositiveWalk flow path.val)
    (nonneg : ∀ u v, 0 ≤ flow u v) (mass : ℚ) (mass_pos : 0 < mass) :
    0 < bottleneck G flow mass path ∧ bottleneck G flow mass path ≤ mass ∧
      (∀ u v, 0 ≤ flow u v - bottleneck G flow mass path * transportVisits path.val u v) ∧
      (bottleneck G flow mass path < mass →
        (positiveArcs (fun u v => flow u v - bottleneck G flow mass path * transportVisits path.val u v)).card <
          (positiveArcs flow).card) := by
  let S := insert mass (path.val.darts.map fun dart => flow dart.fst dart.snd).toFinset
  let amount := bottleneck G flow mass path
  have amount_mem : amount ∈ S := Finset.min'_mem _ _
  have amount_pos : 0 < amount := by
    rcases Finset.mem_insert.mp amount_mem with same | member
    · simpa [same] using mass_pos
    · obtain ⟨dart, member, same⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
      rw [← same]
      exact positive dart member
  have amount_mass : amount ≤ mass := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have amount_arc : ∀ dart ∈ path.val.darts, amount ≤ flow dart.fst dart.snd := by
    intro dart member
    exact Finset.min'_le _ _ (Finset.mem_insert_of_mem (List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨dart, member, rfl⟩)))
  have residual : ∀ u v, 0 ≤ flow u v - amount * transportVisits path.val u v := by
    intro u v
    rw [visits_eq_usesArc]
    split
    · rename_i used
      obtain ⟨dart, member, fst, snd⟩ := (usesArc_iff G path u v).mp used
      have bound := amount_arc dart member
      simpa only [fst, snd, mul_one] using sub_nonneg.mpr bound
    · simpa using nonneg u v
  refine ⟨amount_pos, amount_mass, residual, ?_⟩
  intro smaller
  have arc_mem : amount ∈ (path.val.darts.map fun dart => flow dart.fst dart.snd).toFinset :=
    (Finset.mem_insert.mp amount_mem).resolve_left (ne_of_lt smaller)
  obtain ⟨dart, member, same⟩ := List.mem_map.mp (List.mem_toFinset.mp arc_mem)
  have support_subset : positiveArcs (fun u v => flow u v - amount * transportVisits path.val u v) ⊆ positiveArcs flow := by
    intro entry positive_residual
    simp only [positiveArcs, Finset.mem_filter, Finset.mem_univ, true_and] at *
    have removed := mul_nonneg amount_pos.le (transportVisits_nonneg path.val entry.1 entry.2)
    linarith
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨support_subset, ?_⟩
  intro same_support
  have positive_entry : (dart.fst, dart.snd) ∈ positiveArcs flow := by
    simp only [positiveArcs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact positive dart member
  rw [← same_support] at positive_entry
  have visits := path_transportVisits_dart path dart
  simp only [member, ite_true] at visits
  simp only [positiveArcs, Finset.mem_filter, Finset.mem_univ, true_and] at positive_entry
  rw [visits, same] at positive_entry
  linarith

end BuyAtBulk.Computation.FlowDecomposition
