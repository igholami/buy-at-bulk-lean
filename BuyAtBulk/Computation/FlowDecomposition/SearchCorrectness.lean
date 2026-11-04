import BuyAtBulk.Computation.FlowDecomposition.Search

namespace BuyAtBulk.Computation.FlowDecomposition
open BuyAtBulk.CompactFlow
variable {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

def Valid (flow : V → V → ℚ) {source : V} (table : Table G source) : Prop :=
  ∀ entry ∈ table, PositiveWalk flow entry.2

theorem lookup_valid (flow : V → V → ℚ) {source target : V} (table : Table G source)
    (valid : Valid G flow table) {path : G.Walk source target}
    (returned : lookup G table target = some path) : PositiveWalk flow path := by
  induction table with
  | nil => simp [lookup] at returned
  | cons first rest ih =>
    rcases first with ⟨v, first⟩
    by_cases equal : v = target
    · simp only [lookup, dif_pos equal] at returned
      have same := Option.some.inj returned
      subst path
      have positive := valid ⟨v, first⟩ (List.mem_cons_self ..)
      simpa only [PositiveWalk, SimpleGraph.Walk.darts_copy] using positive
    · simp only [lookup, dif_neg equal] at returned
      exact ih (fun entry member => valid entry (List.mem_cons_of_mem _ member)) returned

theorem concat_positive (flow : V → V → ℚ) {source u target : V}
    (path : G.Walk source u) (edge : G.Adj u target)
    (positive : PositiveWalk flow path) (last : 0 < flow u target) :
    PositiveWalk flow (path.concat edge) := by
  intro dart member
  simp only [SimpleGraph.Walk.darts_concat, List.concat_eq_append, List.mem_append, List.mem_singleton] at member
  rcases member with member | same
  · exact positive dart member
  · subst dart
    exact last

theorem extend_valid (flow : V → V → ℚ) {source target : V} (table : Table G source)
    (valid : Valid G flow table) {path : G.Walk source target}
    (returned : extend G flow table target = some path) : PositiveWalk flow path := by
  induction table with
  | nil => simp [extend] at returned
  | cons first rest ih =>
    rcases first with ⟨v, first⟩
    by_cases edge : G.Adj v target
    · by_cases positive : 0 < flow v target
      · simp only [extend, dif_pos edge, if_pos positive] at returned
        have same := Option.some.inj returned
        subst path
        exact concat_positive G flow first edge (valid _ (List.mem_cons_self ..)) positive
      · simp only [extend, dif_pos edge, if_neg positive] at returned
        exact ih (fun entry member => valid entry (List.mem_cons_of_mem _ member)) returned
    · simp only [extend, dif_neg edge] at returned
      exact ih (fun entry member => valid entry (List.mem_cons_of_mem _ member)) returned

theorem next_valid (flow : V → V → ℚ) {source target : V} (table : Table G source)
    (valid : Valid G flow table) {path : G.Walk source target}
    (returned : next G flow table target = some path) : PositiveWalk flow path := by
  unfold next at returned
  split at returned
  · rename_i actual found
    have same := Option.some.inj returned
    subst path
    exact lookup_valid G flow table valid found
  · exact extend_valid G flow table valid returned

theorem step_valid (flow : V → V → ℚ) {source : V} (table : Table G source)
    (valid : Valid G flow table) : Valid G flow (step G numbering flow table) := by
  intro entry member
  obtain ⟨target, _, returned⟩ := List.mem_filterMap.mp member
  obtain ⟨path, found, equal⟩ := Option.map_eq_some_iff.mp returned
  subst entry
  exact next_valid G flow table valid found

theorem iterate_valid (flow : V → V → ℚ) (source : V) (rounds : ℕ) :
    Valid G flow (iterate G numbering flow source rounds) := by
  induction rounds with
  | zero =>
    intro entry member
    have same : entry = ⟨source, SimpleGraph.Walk.nil⟩ := by simpa [iterate] using member
    subst entry
    simp [PositiveWalk]
  | succ k ih => exact step_valid G numbering flow _ ih

theorem iterate_preserves (flow : V → V → ℚ) (source target : V) (first last : ℕ)
    (bound : first ≤ last) (found : ∃ path, lookup G (iterate G numbering flow source first) target = some path) :
    ∃ path, lookup G (iterate G numbering flow source last) target = some path := by
  induction last, bound using Nat.le_induction with
  | base => exact found
  | succ last bound ih => exact step_preserves G numbering flow _ ih

theorem found_of_positive_walk (flow : V → V → ℚ) {source target : V}
    (path : G.Walk source target) (positive : PositiveWalk flow path) :
    ∃ actual, lookup G (iterate G numbering flow source path.length) target = some actual := by
  induction path using SimpleGraph.Walk.concatRec with
  | Hnil => exact ⟨.nil, by simp [iterate, lookup]⟩
  | @Hconcat source u target path edge ih =>
    have prefixPositive : PositiveWalk flow path := by
      intro dart member
      exact positive dart (by simp [SimpleGraph.Walk.darts_concat, member])
    have lastPositive : 0 < flow u target :=
      positive ⟨(u, target), edge⟩ (by simp [SimpleGraph.Walk.darts_concat])
    simpa only [SimpleGraph.Walk.length_concat, iterate] using
      step_extends G numbering flow (iterate G numbering flow source path.length) (ih prefixPositive) edge lastPositive

theorem positivePath_some (flow : V → V → ℚ) (source target : V)
    (path : G.Path source target) (returned : positivePath G numbering flow source target = some path) :
    PositiveWalk flow path.val := by
  unfold positivePath at returned
  obtain ⟨walk, found, same⟩ := Option.map_eq_some_iff.mp returned
  subst path
  have positive := lookup_valid G flow _ (iterate_valid G numbering flow source n) found
  intro dart member
  exact positive dart (walk.darts_toPath_subset_darts member)

/-- The finite directed search returns a real positive path whenever positive
flow conservation guarantees one. The existential cut proof is used only for
correctness, never to select the algorithm's returned data. -/
theorem positivePath_exists (flow : V → V → ℚ) (source target : V) (mass : ℚ)
    (mass_pos : 0 < mass) (nonneg : ∀ u v, 0 ≤ flow u v)
    (nonedge : ∀ u v, ¬G.Adj u v → flow u v = 0)
    (balance : ∀ v, (∑ u, flow v u) - (∑ u, flow u v) =
      mass * ((if source = v then 1 else 0) - (if target = v then 1 else 0))) :
    ∃ path, positivePath G numbering flow source target = some path := by
  obtain ⟨witness, positive⟩ := positive_path_of_balance flow source target mass mass_pos nonneg nonedge (by
    intro v
    by_cases hs : source = v <;> by_cases ht : target = v <;> simpa [hs, ht] using balance v)
  have found := found_of_positive_walk G numbering flow witness.val positive
  have length := witness.property.length_lt
  have found' := iterate_preserves G numbering flow source target witness.val.length n (by
    simpa only [numbered_card numbering] using Nat.le_of_lt length) found
  obtain ⟨walk, returned⟩ := found'
  exact ⟨walk.toPath, by simp [positivePath, returned]⟩

end BuyAtBulk.Computation.FlowDecomposition
