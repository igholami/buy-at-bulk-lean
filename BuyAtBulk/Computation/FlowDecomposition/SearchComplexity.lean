import BuyAtBulk.Computation.FlowDecomposition.SearchCorrectness

/-! Bounds on the materialized walk tables. These account for path-copy sizes
as well as the number of entries inspected by directed breadth expansion. -/
namespace BuyAtBulk.Computation.FlowDecomposition
variable {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

def Depth {source : V} (table : Table G source) (rounds : ℕ) : Prop :=
  ∀ entry ∈ table, entry.2.length ≤ rounds

theorem lookup_depth {source target : V} (table : Table G source) (rounds : ℕ)
    (depth : Depth G table rounds) {path : G.Walk source target}
    (returned : lookup G table target = some path) : path.length ≤ rounds := by
  induction table with
  | nil => simp [lookup] at returned
  | cons first rest ih =>
    rcases first with ⟨v, first⟩
    by_cases equal : v = target
    · simp only [lookup, dif_pos equal] at returned
      have same := Option.some.inj returned
      subst path
      simpa only [SimpleGraph.Walk.length_copy] using depth ⟨v, first⟩ (List.mem_cons_self ..)
    · simp only [lookup, dif_neg equal] at returned
      exact ih (fun entry member => depth entry (List.mem_cons_of_mem _ member)) returned

theorem extend_depth (flow : V → V → ℚ) {source target : V} (table : Table G source)
    (rounds : ℕ) (depth : Depth G table rounds) {path : G.Walk source target}
    (returned : extend G flow table target = some path) : path.length ≤ rounds + 1 := by
  induction table with
  | nil => simp [extend] at returned
  | cons first rest ih =>
    rcases first with ⟨v, first⟩
    by_cases edge : G.Adj v target
    · by_cases positive : 0 < flow v target
      · simp only [extend, dif_pos edge, if_pos positive] at returned
        have same := Option.some.inj returned
        subst path
        simpa only [SimpleGraph.Walk.length_concat] using Nat.succ_le_succ (depth ⟨v, first⟩ (List.mem_cons_self ..))
      · simp only [extend, dif_pos edge, if_neg positive] at returned
        exact ih (fun entry member => depth entry (List.mem_cons_of_mem _ member)) returned
    · simp only [extend, dif_neg edge] at returned
      exact ih (fun entry member => depth entry (List.mem_cons_of_mem _ member)) returned

theorem step_depth (flow : V → V → ℚ) {source : V} (table : Table G source)
    (rounds : ℕ) (depth : Depth G table rounds) : Depth G (step G numbering flow table) (rounds + 1) := by
  intro entry member
  obtain ⟨target, _, returned⟩ := List.mem_filterMap.mp member
  obtain ⟨path, found, equal⟩ := Option.map_eq_some_iff.mp returned
  subst entry
  unfold next at found
  split at found
  · rename_i actual old
    have same := Option.some.inj found
    subst path
    exact (lookup_depth G table rounds depth old).trans (Nat.le_succ _)
  · exact extend_depth G flow table rounds depth found

theorem iterate_depth (flow : V → V → ℚ) (source : V) (rounds : ℕ) :
    Depth G (iterate G numbering flow source rounds) rounds := by
  induction rounds with
  | zero =>
    intro entry member
    have equal : entry = ⟨source, SimpleGraph.Walk.nil⟩ := by simpa [iterate] using member
    subst entry
    exact le_rfl
  | succ k ih => exact step_depth G numbering flow _ k ih

theorem iterate_length (flow : V → V → ℚ) (source : V) (rounds : ℕ) :
    (iterate G numbering flow source rounds).length ≤ n := by
  cases rounds with
  | zero => simpa [iterate] using (show 1 ≤ n by have := (numbering source).isLt; omega)
  | succ k => exact step_length G numbering flow _

theorem table_cells {source : V} (table : Table G source) (rounds : ℕ)
    (depth : Depth G table rounds) : (table.map fun entry => entry.2.length).sum ≤ table.length * rounds := by
  induction table with
  | nil => simp
  | cons entry rest ih =>
    have first := depth entry (List.mem_cons_self ..)
    have rest := ih (fun entry member => depth entry (List.mem_cons_of_mem _ member))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

/-- At most n walks of at most k edges are stored after k rounds. In
particular the final search table stores at most n² walk-edge cells. -/
theorem search_storage (flow : V → V → ℚ) (source : V) (rounds : ℕ) :
    (iterate G numbering flow source rounds).length ≤ n ∧
    ((iterate G numbering flow source rounds).map fun entry => entry.2.length).sum ≤ n * rounds := by
  have entries := iterate_length G numbering flow source rounds
  refine ⟨entries, ?_⟩
  exact (table_cells G _ rounds (iterate_depth G numbering flow source rounds)).trans (Nat.mul_le_mul_right rounds entries)

end BuyAtBulk.Computation.FlowDecomposition
